#include <LIEF/LIEF.hpp>
#include <vector>
#include <cstdint>

extern "C" {

typedef void ELFHandle;

ELFHandle* lief_parse(const char* filepath) {
    return LIEF::ELF::Parser::parse(filepath).release();
}

ELFHandle* lief_parse_mem(const uint8_t *data, size_t elements) {
    return LIEF::ELF::Parser::parse(std::vector<uint8_t>(data, data + elements)).release();
}

const uint32_t* lief_get_text(ELFHandle* handle, size_t* out_elements, uint64_t* va) {
    auto bin = static_cast<LIEF::ELF::Binary*>(handle);
    for (LIEF::ELF::Segment& seg : bin->segments()) {
        if (seg.has(LIEF::ELF::Segment::FLAGS::X)) {
            auto content = seg.content();
            *out_elements = content.size() / 4;
            *va = seg.virtual_address();
            return reinterpret_cast<const uint32_t*>(content.data());
        }
    }
    *out_elements = 0;
    return nullptr;
}

uint64_t lief_get_after(ELFHandle* handle) {
    auto elf = static_cast<LIEF::ELF::Binary*>(handle);
    uint64_t max = 0;
    for (LIEF::ELF::Segment& seg : elf->segments()) {
        max = std::max(max, seg.virtual_address() + seg.virtual_size());
    }
    // lief will put the phdr after, so skip one additional page
    return ((max >> 12) + 2) << 12;
}

uint64_t lief_get_entrypoint(ELFHandle* handle) {
    return static_cast<LIEF::ELF::Binary*>(handle)->header().entrypoint();
}

void lief_set_nx(ELFHandle* handle) {
    auto elf = static_cast<LIEF::ELF::Binary*>(handle);
    for (LIEF::ELF::Segment& seg : elf->segments()) {
        if (seg.has(LIEF::ELF::Segment::FLAGS::X)) {
            uint32_t flags = static_cast<uint32_t>(seg.flags());
            flags &= ~static_cast<uint32_t>(LIEF::ELF::Segment::FLAGS::X);
            seg.flags(flags);
        }
    }
}

void lief_set_entrypoint(ELFHandle* handle, uint64_t entrypoint) {
    static_cast<LIEF::ELF::Binary*>(handle)->header().entrypoint(entrypoint);
}

bool lief_add_segment(ELFHandle* handle, const uint32_t* data, size_t elements, uint64_t va) {
    auto bin = static_cast<LIEF::ELF::Binary*>(handle);

    LIEF::ELF::Segment new_seg;
    new_seg.type(LIEF::ELF::Segment::TYPE::LOAD);
    uint32_t rx_flags = static_cast<uint32_t>(LIEF::ELF::Segment::FLAGS::R) |
                        static_cast<uint32_t>(LIEF::ELF::Segment::FLAGS::X);
    new_seg.flags(rx_flags);

    auto byte_ptr = reinterpret_cast<const uint8_t*>(data);
    size_t byte_size = elements * 4;
    new_seg.content(std::vector<uint8_t>(byte_ptr, byte_ptr + byte_size));
    new_seg.virtual_address(va);
    return bin->add(new_seg) != nullptr;
}

void lief_write_and_free(ELFHandle* handle, const char* out_path) {
    auto bin = static_cast<LIEF::ELF::Binary*>(handle);
    bin->write(out_path);
    delete bin;
}

typedef uint64_t (*rel_t)(uint64_t old_address);

void lief_update_symbols(ELFHandle* handle, rel_t rel) {
    auto bin = static_cast<LIEF::ELF::Binary*>(handle);

    for (LIEF::ELF::Symbol& sym : bin->symbols()) {
        if (sym.type() == LIEF::ELF::Symbol::TYPE::FUNC && sym.value() != 0) {
            assert((sym.value() & 0b11) == 0);
            auto start = rel(sym.value() >> 2) << 2;
            auto end = rel((sym.value() + sym.size()) >> 2) << 2;
            sym.value(start);
            sym.size(end - start);
        }
    }
    for (LIEF::ELF::Symbol& sym : bin->dynamic_symbols()) {
        if (sym.type() == LIEF::ELF::Symbol::TYPE::FUNC && sym.value() != 0) {
            assert((sym.value() & 0b11) == 0);
            sym.value(rel(sym.value() >> 2) << 2);
        }
    }

    auto txt = bin->get_section(".text");
    if (txt != nullptr) {
        auto start = rel(txt->virtual_address() >> 2) << 2;
        auto end = rel((txt->virtual_address() + txt->size()) >> 2) << 2;
        txt->virtual_address(start);
        txt->size(end - start);
    }
}

void lief_update_dynamic_entry(ELFHandle* handle, rel_t rel) {
    auto bin = static_cast<LIEF::ELF::Binary*>(handle);
    using TAG = LIEF::ELF::DynamicEntry::TAG;
    if (auto* init = bin->get(TAG::INIT)) {
        auto val = rel(init->value() >> 2) << 2;
        init->value(val);
    }
    if (auto* fini = bin->get(TAG::FINI)) {
        auto val = rel(fini->value() >> 2) << 2;
        fini->value(val);
    }
    if (auto* init_array = dynamic_cast<LIEF::ELF::DynamicEntryArray*>(bin->get(TAG::INIT_ARRAY))) {
        std::vector<uint64_t>& arr = init_array->array();
        for (uint64_t& val : arr) {
            val = rel(val >> 2) << 2;
        }
    }
    if (auto* fini_array = dynamic_cast<LIEF::ELF::DynamicEntryArray*>(bin->get(TAG::FINI_ARRAY))) {
        std::vector<uint64_t>& arr = fini_array->array();
        for (uint64_t& val : arr) {
            val = rel(val >> 2) << 2;
        }
    }
}

// force the linker to keep this file in the archive
void _force_link() {}

}
