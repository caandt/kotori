import json
import itertools
import mmap
import struct
import argparse
import code
from pprint import pprint
from pathlib import Path
from collections import defaultdict

def read_policy(mm):
    res = defaultdict(set)
    nrets, = struct.unpack("<q", mm[8:16]);
    for n in range(nrets):
        start = 24 + n * 64
        while start:
            *vals, start = struct.unpack("<8q", mm[start:start+64])
            vals = [x for x in vals if x]
            if vals:
                res[n].update(vals)
    return res

def read_count(mm):
    res = {}
    offset = 8 + 24 * 16
    for start, stop, size in struct.iter_unpack("<3q", mm[8:offset]):
        if stop == 0:
            break
        for n in range(size):
            cnt, = struct.unpack("<q", mm[offset:offset+8])
            if cnt:
                res[start + 4 * n] = cnt
            offset += 8
    return res

def read_data(path):
    with open(path, "rb") as f:
        with mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ) as mm:
            magic, = struct.unpack("<q", mm[0:8]);
            if magic == 0x7963696c6f70a8a8:
                return read_policy(mm)
            elif magic == 0x7963696c6f70a822:
                return read_count(mm)
            else:
                raise Exception("unknown file type")


class Table:
    def __init__(self, d):
        self.hash = d['hash']
        self.tbl = d['tbl']
        self.ti = d['ti']

    def h(self, x):
        return (x >> self.hash[0]) & ((1 << self.hash[1]) - 1)

    def __getitem__(self, x):
        return self.tbl[self.h(x)]

    def __repr__(self):
        return f'T[{len(self.tbl)}]@{hex(self.ti*4)}'

    def __contains__(self, x):
        return x in self.tbl

class Data:
    def __init__(self, p: Path):
        d = json.loads(p.read_text())
        self.bi = d['bi']
        self.bip = d["bi'"]
        self.bti = d['bti']
        self.ai = d['ai']
        self.len = d['len']
        self.devs = list(itertools.batched(d['devs'], 2))
        self.dsets = d['dsets']
        self.tc = list(map(Table, d['tc']))
        self._pol = d['pol']
        self.rets = d['rets']

    def pol(self, x):
        try:
            return next(b for [a,b] in self._pol if a == x)
        except:
            raise

    def _rel(self, x):
        low = 0
        high = len(self.devs) - 1
        ans = -1
        while low <= high:
            mid = low + (high - low) // 2
            if self.devs[mid][0] < x:
                ans = mid
                low = mid + 1
            else:
                high = mid - 1
        if ans == -1:
            return x
        return x + self.devs[ans][1]

    def rel(self, x):
        if self.bi <= x < self.bi + self.len:
            return self._rel(x - self.bi) + self.bip
        return x

    def rela(self, x):
        return self.rel(x // 4) * 4

    def _irel(self, x):
        if not self.devs or x < 0:
            return x
        low = 0
        high = len(self.devs) - 1
        ans = -1
        while low <= high:
            mid = low + (high - low) // 2
            i_mid = self.devs[mid][0]
            C_prev = self.devs[mid - 1][1] if mid > 0 else 0
            S_mid = i_mid + C_prev
            if S_mid <= x:
                ans = mid
                low = mid + 1
            else:
                high = mid - 1
        if ans == -1:
            return x
        i_ans = self.devs[ans][0]
        C_ans = self.devs[ans][1]
        E_ans = i_ans + C_ans
        if x <= E_ans:
            return i_ans
        else:
            return x - C_ans

    def irel(self, x):
        if self.bip <= x < self.ai:
            return self._irel(x - self.bip) + self.bi
        return x

    def irela(self, x):
        return self.irel(x // 4) * 4

    def retlookup(self, x):
        return self.rets.index(self.irela(x)//4)

if __name__ == '__main__':
    parse = argparse.ArgumentParser()
    parse.add_argument("json", type=Path, nargs="?")
    parse.add_argument("-p", "--pol", type=Path)
    args = parse.parse_args()
    j = Data(args.json) if args.json else None
    p = read_data(args.pol) if args.pol else None
    try:
        import _pyrepl.main
        _pyrepl.main.interactive_console()
    except ImportError:
        import code
        code.interact(local=globals())
