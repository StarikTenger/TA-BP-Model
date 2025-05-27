#include "Util.h"
#include <algorithm>
#include <iostream>

int random_int(int min, int max) {
    return rand() % (max - min + 1) + min;
}

bool next_mask(std::vector<bool>& mask) {
    for (int i = mask.size() - 1; i >= 0; --i) {
        if (!mask[i]) {
            mask[i] = true;
            return true;
        }
        mask[i] = false;
    }
    return false;
}

MaskGenerator::MaskGenerator(int size) {
    mask.resize(size, false);
    restriction.resize(size, false);
    pending_restriction.resize(size, false); // <-- initialize
    aux_mask.resize(size, false);
    level = 1;
    update_aux();
    first = false;
}

void MaskGenerator::restrict(const std::vector<bool> &r)
{
    if (pending_restriction.empty()) pending_restriction.resize(mask.size(), false);
    for (size_t i = 0; i < mask.size(); ++i) {
        pending_restriction[i] = pending_restriction[i] || r[i];
    }
}

void MaskGenerator::restrict_last() {
    restrict(mask);
}

std::vector<bool> &MaskGenerator::get_mask() const {
    return const_cast<std::vector<bool>&>(mask);
}

void MaskGenerator::update_aux() {
    // Apply pending_restriction to restriction when moving to a new level
    if (!pending_restriction.empty()) {
        for (size_t i = 0; i < restriction.size(); ++i) {
            restriction[i] = restriction[i] || pending_restriction[i];
        }
        std::fill(pending_restriction.begin(), pending_restriction.end(), false);
    }

    std::cout << "restriction: ";
    for (bool r : restriction) std::cout << r;
    std::cout << std::endl;
    std::cout << "level: " << level << std::endl;

    // Count non-restricted positions
    free_count = 0;
    for (bool r : restriction) if (!r) ++free_count;
    aux_mask.assign(free_count, false);
    // Set first 'level' bits to 1
    for (int i = 0; i < std::min(level, free_count); ++i)
        aux_mask[i] = true;
    std::sort(aux_mask.begin(), aux_mask.end()); // Ensure lex order
    first = true;
    if (level > free_count) return;
    map_aux_to_mask();
}

bool MaskGenerator::next_aux() {
    bool res = std::next_permutation(aux_mask.begin(), aux_mask.end());
    std::cout << "Next aux " << res << "\n";
    std::cout << "aux_mask: ";
    for (bool b : aux_mask) std::cout << b;
    std::cout << "\n";
    if (res)
        map_aux_to_mask();
    return res;
}

void MaskGenerator::map_aux_to_mask() {
    size_t n = mask.size();
    mask.assign(n, false);
    int aux_idx = 0;
    for (size_t i = 0; i < n; ++i) {
        if (!restriction[i]) {
            if (aux_idx < (int)aux_mask.size() && aux_mask[aux_idx])
                mask[i] = true;
            ++aux_idx;
        }
    }
}

bool MaskGenerator::next() {
    size_t n = mask.size();
    if (restriction.empty()) restriction.resize(n, false);

    // On first call or after level/restriction change, initialize aux
    if (first) {
        update_aux();
        first = false;
    }

    while (true) {
        // Map aux_mask to mask, skipping restricted positions

        if (first) { 
            return true; 
        }

        // Try next aux_mask
        if (!next_aux()) {
            ++level;
            update_aux();
            if (level > free_count) return false;
            continue;
        }

        return true;
    }
}

