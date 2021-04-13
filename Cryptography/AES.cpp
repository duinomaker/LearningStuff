#include <iomanip>
#include <iostream>
#include <cstdint>

uint8_t multiply_polynomials(uint8_t a, uint8_t b) {
    uint8_t x = a;
    a = 0;
    while (b) {
        if (b & 1) {
            a ^= x;
        }
        x = x & 0x80 ?
            (x << 1) ^ 0x1b :
            x << 1;
        b >>= 1;
    }
    return a;
}

struct KeyBlock {
    friend std::ostream &operator<<(std::ostream &out, KeyBlock const &blk);

public:
    explicit KeyBlock(uint8_t const *slice);

    uint32_t const *columns() { return data; }

    void next();

private:
    uint32_t data[4];

    uint8_t r_con;
};

struct Block {
    friend std::ostream &operator<<(std::ostream &out, Block const &blk);

public:
    explicit Block(uint8_t const *slice);

    void shift_rows();

    void shift_rows_inv();

    void substitute();

    void substitute_inv();

    void mix_columns();

    void mix_columns_inv();

    void add_round_key(const uint32_t columns[]);

    static uint8_t const s_box[256];

    static uint8_t const s_box_inv[256];

    void read_into(uint8_t *dst) const;

private:
    uint8_t data[4][4];

    void substitute_impl(uint8_t const box[]);

    void mix_columns_impl(uint8_t const matrix[][4]);
};

Block::Block(const uint8_t *slice)
        : data() {
    memcpy(data, slice, 16 * sizeof(uint8_t));
}

void Block::read_into(uint8_t *dst) const {
    memcpy(dst, data, 16 * sizeof(uint8_t));
}

uint8_t const Block::s_box[256] = {
        0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
        0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
        0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
        0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
        0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
        0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
        0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
        0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
        0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
        0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
        0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
        0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
        0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
        0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
        0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
        0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16};

uint8_t const Block::s_box_inv[256] = {
        0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
        0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
        0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
        0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
        0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
        0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
        0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
        0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
        0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
        0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
        0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
        0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
        0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
        0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
        0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
        0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d};

std::ostream &operator<<(std::ostream &out, Block const &blk) {
    out << std::hex;
    for (size_t i = 0; i != 4; ++i) {
        for (size_t j = 0; j != 4; ++j) {
            out << std::setw(2) << std::setfill('0')
                << (unsigned int) blk.data[i][j] << ' ';
        }
        if (i != 3) {
            out << '\n';
        }
    }
    out << std::dec;
    return out;
}

void Block::shift_rows() {
    *(uint32_t *) data[1] = (*(uint32_t *) data[1] << 24) | (*(uint32_t *) data[1] >> 8);
    *(uint32_t *) data[2] = (*(uint32_t *) data[2] << 16) | (*(uint32_t *) data[2] >> 16);
    *(uint32_t *) data[3] = (*(uint32_t *) data[3] << 8) | (*(uint32_t *) data[3] >> 24);
}

void Block::shift_rows_inv() {
    *(uint32_t *) data[1] = (*(uint32_t *) data[1] << 8) | (*(uint32_t *) data[1] >> 24);
    *(uint32_t *) data[2] = (*(uint32_t *) data[2] << 16) | (*(uint32_t *) data[2] >> 16);
    *(uint32_t *) data[3] = (*(uint32_t *) data[3] << 24) | (*(uint32_t *) data[3] >> 8);
}

void Block::substitute() {
    substitute_impl(s_box);
}

void Block::substitute_inv() {
    substitute_impl(s_box_inv);
}

void Block::substitute_impl(const uint8_t *box) {
    for (size_t i = 0; i != 4; ++i) {
        for (size_t j = 0; j != 4; ++j) {
            data[i][j] = box[data[i][j]];
        }
    }
}

void Block::mix_columns() {
    static uint8_t const matrix[4][4] = {0x02, 0x03, 0x01, 0x01,
                                         0x01, 0x02, 0x03, 0x01,
                                         0x01, 0x01, 0x02, 0x03,
                                         0x03, 0x01, 0x01, 0x02};
    mix_columns_impl(matrix);
}

void Block::mix_columns_inv() {
    static uint8_t const matrix[4][4] = {0x0e, 0x0b, 0x0d, 0x09,
                                         0x09, 0x0e, 0x0b, 0x0d,
                                         0x0d, 0x09, 0x0e, 0x0b,
                                         0x0b, 0x0d, 0x09, 0x0e};
    mix_columns_impl(matrix);
}

void Block::mix_columns_impl(uint8_t const matrix[][4]) {
    uint8_t result[4][4]{};
    for (size_t i = 0; i != 4; ++i) {
        for (size_t j = 0; j != 4; ++j) {
            for (size_t k = 0; k != 4; ++k) {
                result[i][j] ^= multiply_polynomials(matrix[i][k], data[k][j]);
            }
        }
    }
    memcpy(data, result, 16 * sizeof(uint8_t));
}

void Block::add_round_key(uint32_t const columns[]) {
    for (size_t i = 0; i != 4; ++i) {
        for (size_t j = 0; j != 4; ++j) {
            data[i][j] ^= (columns[j] >> ((3 - i) * 8)) & 0xff;
        }
    }
}

KeyBlock::KeyBlock(uint8_t const *slice)
        : data(), r_con(0x01) {
    for (size_t i = 0; i != 4; ++i) {
        for (size_t j = 0; j != 4; ++j) {
            data[i] |= slice[i * 4 + j] << ((3 - j) * 8);
        }
    }
}

std::ostream &operator<<(std::ostream &out, const KeyBlock &blk) {
    out << std::hex;
    for (size_t i = 0; i != 4; ++i) {
        for (size_t j = 0; j != 4; ++j) {
            out << std::setw(2) << std::setfill('0')
                << (unsigned int) (blk.data[j] >> ((3 - i) * 8) & 0xff) << ' ';
        }
        if (i != 3) {
            out << '\n';
        }
    }
    out << std::dec;
    return out;
}

void KeyBlock::next() {
    data[0] ^= (Block::s_box[(data[3] >> 0) & 0xff] << 8)
               | (Block::s_box[(data[3] >> 8) & 0xff] << 16)
               | (Block::s_box[(data[3] >> 16) & 0xff] << 24)
               | (Block::s_box[(data[3] >> 24) & 0xff] << 0)
                 ^ (r_con << 24);
    data[1] ^= data[0];
    data[2] ^= data[1];
    data[3] ^= data[2];
    r_con = multiply_polynomials(r_con, 0x2);
}

size_t AES128_encoded_size(size_t bytes) {
    return bytes % 16 == 0 ?
           sizeof(size_t) + bytes :
           sizeof(size_t) + (bytes / 16 + 1) * 16;
}

size_t AES128_decoded_size(uint8_t *buffer) {
    size_t size;
    memcpy(&size, buffer, sizeof(size_t));
    return size;
}

void AES128_encode_block(uint8_t const *key_slice,
                         uint8_t *block_data) {
    KeyBlock key_blk(key_slice);
    Block blk(block_data);
    blk.add_round_key(key_blk.columns());
    for (int i = 0; i != 9; ++i) {
        blk.substitute();
        blk.shift_rows();
        blk.mix_columns();
        key_blk.next();
        blk.add_round_key(key_blk.columns());
    }
    blk.substitute();
    blk.shift_rows();
    key_blk.next();
    blk.add_round_key(key_blk.columns());
    blk.read_into(block_data);
}

void AES128_decode_block(uint8_t const *key_slice,
                         uint8_t *block_data) {
    KeyBlock key_blk(key_slice);
    Block blk(block_data);
    uint32_t key_blocks_columns[10][4];
    for (size_t i = 0; i != 10; ++i) {
        memcpy(key_blocks_columns[i], key_blk.columns(), 4 * sizeof(uint32_t));
        key_blk.next();
    }
    blk.add_round_key(key_blk.columns());
    for (size_t i = 9; i != 0; --i) {
        blk.substitute_inv();
        blk.shift_rows_inv();
        blk.add_round_key(key_blocks_columns[i]);
        blk.mix_columns_inv();
    }
    blk.substitute_inv();
    blk.shift_rows_inv();
    blk.add_round_key(key_blocks_columns[0]);
    blk.read_into(block_data);
}

void AES128_encode(uint8_t const *key_slice,
                   uint8_t const *data_slice, size_t size,
                   uint8_t *buffer) {
    uint8_t const *ptr_data = data_slice;
    uint8_t *ptr = buffer;
    memcpy(ptr, &size, sizeof(size_t));
    ptr += sizeof(size_t);
    for (size_t i = 0; i < size; i += 16) {
        memcpy(ptr, ptr_data, 16 * sizeof(uint8_t));
        AES128_encode_block(key_slice, ptr);
        ptr += 16 * sizeof(uint8_t);
        ptr_data += 16 * sizeof(uint8_t);
    }
    if (size % 16) {
        size_t rem = (16 - size % 16) * sizeof(uint8_t);
        uint8_t temp[16]{};
        memcpy(temp, ptr_data, rem);
        AES128_encode_block(key_slice, temp);
        memcpy(ptr, temp, rem);
    }
}

void AES128_decode(uint8_t const *key_slice,
                   uint8_t const *data_slice,
                   uint8_t *buffer) {
    uint8_t const *ptr_data = data_slice;
    uint8_t *ptr = buffer;
    size_t size;
    memcpy(&size, ptr_data, sizeof(size_t));
    ptr_data += sizeof(size_t);
    for (size_t i = 0; i < size; i += 16) {
        memcpy(ptr, ptr_data, 16 * sizeof(uint8_t));
        AES128_decode_block(key_slice, ptr);
        ptr += 16 * sizeof(uint8_t);
        ptr_data += 16 * sizeof(uint8_t);
    }
    if (size % 16) {
        size_t rem = (16 - size % 16) * sizeof(uint8_t);
        uint8_t temp[16]{};
        memcpy(temp, ptr_data, 16 * sizeof(uint8_t));
        AES128_decode_block(key_slice, temp);
        memcpy(ptr, temp, rem);
    }
}

void display_bytes(uint8_t const *slice, size_t size) {
    std::cout << std::hex;
    for (size_t i = 0; i != size; ++i) {
        std::cout << std::setw(2) << std::setfill('0')
                  << (unsigned int) slice[i] << ' ';
    }
    std::cout << std::endl << std::dec;
}

void simple_test() {
    auto key_slice = reinterpret_cast<uint8_t const *>(
            "\x3c\xa1\x0b\x21\x57\xf0\x19\x16\x90\x2e\x13\x80\xac\xc1\x07\xbd");
    auto plain = reinterpret_cast<uint8_t const *>(
            "The AES-128 algorithm, implemented by B19031232 Yuxuan Dai.");
    size_t plain_size = strlen(reinterpret_cast<const char *>(plain) + 1);
    printf("%s\n", plain);
    size_t encoded_size = AES128_encoded_size(plain_size);
    auto encoded = new uint8_t[encoded_size];
    AES128_encode(key_slice, plain, plain_size, encoded);

    size_t decoded_size = AES128_decoded_size(encoded);
    auto decoded = new uint8_t[decoded_size];
    AES128_decode(key_slice, encoded, decoded);
    printf("%s\n", decoded);

    delete[] encoded;
    delete[] decoded;
}

void xor_experiment() {
    auto AES128_encode_block = [](uint8_t const *key_slice,
                                  uint8_t *block_data, int rounds) {
        KeyBlock key_blk(key_slice);
        Block blk(block_data);
        blk.add_round_key(key_blk.columns());
        for (int i = 1; i != rounds; ++i) {
            blk.substitute();
            blk.shift_rows();
            blk.mix_columns();
            key_blk.next();
            blk.add_round_key(key_blk.columns());
        }
        blk.substitute();
        blk.shift_rows();
        key_blk.next();
        blk.add_round_key(key_blk.columns());
        blk.read_into(block_data);
    };
    auto key_slice = reinterpret_cast<uint8_t const *>(
            "\x3c\xa1\x0b\x21\x57\xf0\x19\x16\x90\x2e\x13\x80\xac\xc1\x07\xbd");
    uint8_t plain[16]{};
    uint8_t temp[16];
    uint8_t result[16]{};
    for (int rounds = 1; rounds != 5; ++rounds) {
        for (uint16_t i = 0; i != 256; ++i) {
            plain[0] = i;
            memcpy(temp, plain, 16);
            AES128_encode_block(key_slice, temp, rounds);
            *(uint64_t *) result ^= *(uint64_t *) temp;
            *(uint64_t *) (result + 8) ^= *(uint64_t *) (temp + 8);
        }
        std::cout << rounds << " Rounds:\n" << Block(result) << "\n\n";
    }
    std::cout << std::flush;
}

int main() {
    simple_test();
    printf("--------------------------------------------------------------------------------\n");
    xor_experiment();

    return 0;
}
