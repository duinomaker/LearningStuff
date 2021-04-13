#include <cstdio>
#include <utility>
#include <vector>
#include "huffman_tree.h"

struct WeightEntry {
    char ch;
    int weight;
};

char *dump_into_buffer(void const *value, size_t size, char *buffer) {
    memcpy(buffer, value, size);
    buffer += size;
    return buffer;
}

char const *load_from_buffer(char const *buffer, void *value, size_t size) {
    memcpy(value, buffer, size);
    buffer += size;
    return buffer;
}

size_t weights_sector_size(
        std::vector<std::pair<char, int>> const &weights) {
    return sizeof(unsigned char)
           + weights.size() * sizeof(WeightEntry);
}

char *dump_to_weights_sector(
        std::vector<std::pair<char, int>> const &weights,
        char *buffer) {
    unsigned char size = weights.size();
    buffer = dump_into_buffer(&size, sizeof(unsigned char), buffer);
    auto *entries = (WeightEntry *) buffer;
    for (auto &weight: weights) {
        (*entries).ch = weight.first;
        (*entries).weight = weight.second;
        ++entries;
    }
    return (char *) entries;
}

char const *load_from_weights_sector(
        char const *buffer, std::vector<std::pair<char, int>> &weights) {
    unsigned char size;
    buffer = load_from_buffer(buffer, &size, sizeof(unsigned char));
    weights.reserve(weights.size() + size);
    auto *entries = (WeightEntry *) buffer;
    for (unsigned char i = 0; i != size; ++i, ++entries) {
        weights.emplace_back((*entries).ch, (*entries).weight);
    }
    return (const char *) entries;
}

size_t binary_sector_size(std::vector<bool> const &binary) {
    size_t size = binary.size();
    return size % 8 == 0 ?
           size / 8 + sizeof(size_t) :
           size / 8 + sizeof(size_t) + 1;
}

char *dump_to_binary_sector(
        std::vector<bool> const &binary, char *buffer) {
    size_t size = binary.size();
    buffer = dump_into_buffer(&size, sizeof(size_t), buffer);
    unsigned char temp = '\0';
    for (size_t i = 0; i != size; ++i) {
        if (binary[i]) {
            temp |= 1 << (7 - i % 8);
        }
        if ((i + 1) % 8 == 0) {
            *buffer++ = (char) temp;
            temp = '\0';
        }
    }
    *buffer++ = (char) temp;
    return buffer;
}

char const *load_from_binary_sector(
        char const *buffer, std::vector<bool> &binary) {
    size_t size;
    buffer = load_from_buffer(buffer, &size, sizeof(size_t));
    binary.reserve(binary.size() + size);
    for (size_t i = 0; i != size; ++i) {
        binary.push_back(*buffer & (1 << (7 - i % 8)));
        if ((i + 1) % 8 == 0) {
            ++buffer;
        }
    }
    return ++buffer;
}

void load_from_file(char const *filename, char **buffer, size_t *size) {
    FILE *file = fopen(filename, "r");
    fseek(file, 0, SEEK_END);
    *size = ftell(file);
    *buffer = new char[*size];
    rewind(file);
    fread(*buffer, sizeof(char), *size, file);
}

void save_to_file(char const *buffer, size_t size, char const *filename) {
    FILE *file = fopen(filename, "w");
    fwrite(buffer, sizeof(char), size, file);
}

void encode_file(char const *in_file, char const *out_file) {
    char *data;
    size_t size;
    load_from_file(in_file, &data, &size);
    auto weights = statistical_analyze(data, size);
    auto h_tree = minimal_huffman_tree(weights.data(), weights.size());
    auto binary = huffman::encode(h_tree, data, size);

    delete[] data;

    size_t buffer_size = weights_sector_size(weights)
                         + binary_sector_size(binary);
    auto *buffer = new char[buffer_size];
    auto *ptr = buffer;
    ptr = dump_to_weights_sector(weights, ptr);
    dump_to_binary_sector(binary, ptr);
    save_to_file(buffer, buffer_size, out_file);

    delete[] buffer;
}

void decode_file(char const *in_file, char const *out_file) {
    char *buffer;
    size_t size;
    load_from_file(in_file, &buffer, &size);
    char const *ptr = buffer;
    std::vector<std::pair<char, int>> weights;
    std::vector<bool> binary;
    ptr = load_from_weights_sector(ptr, weights);
    load_from_binary_sector(ptr, binary);

    delete[] buffer;

    auto h_tree = minimal_huffman_tree(weights.data(), weights.size());
    auto plain = huffman::decode(h_tree, binary);
    save_to_file(plain.data(), plain.size(), out_file);
}

int main() {
    encode_file("the wisdom of life.txt",
                "the wisdom of life_encoded.txt");
    decode_file("the wisdom of life_encoded.txt",
                "the wisdom of life_decoded.txt");
}