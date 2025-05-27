#include "Util.h"
#include <algorithm>
#include <iostream>
#include <numeric> // for std::iota

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

// Helper: checks if mask matches restriction (ones in restriction must be ones in mask)
static bool matches_restriction(const std::vector<bool>& mask, const std::vector<bool>& restriction) {
    for (size_t i = 0; i < mask.size(); ++i) {
        if (restriction[i] && !mask[i]) return false;
    }
    return true;
}

MaskGenerator::MaskGenerator(int size)
    : mask(size, false), level(1), first(true) {}

void MaskGenerator::restrict(const std::vector<bool>& restriction) {
    restrictions.push_back(restriction);
}

void MaskGenerator::restrict_last() {
    restrictions.push_back(mask);
}

std::vector<bool>& MaskGenerator::get_mask() const {
    // const_cast is safe here because we return a reference to internal mask for reading
    return const_cast<std::vector<bool>&>(mask);
}

// Helper to initialize mask for a given level (number of ones)
void MaskGenerator::init_level() {
    std::fill(mask.begin(), mask.end(), false);
    for (int i = 0; i < level && i < static_cast<int>(mask.size()); ++i) mask[i] = true;
    std::sort(mask.begin(), mask.end());
}

bool MaskGenerator::next() {
    int n = mask.size();
    if (n == 0) return false;

    // On first call, initialize to first mask with 'level' ones
    if (first) {
        init_level();
        first = false;
        // If restricted, skip to next valid
        while (std::any_of(restrictions.begin(), restrictions.end(),
                           [&](const std::vector<bool>& r) { return matches_restriction(mask, r); })) {
            if (!next()) return false;
        }
        return true;
    }

    // Generate next permutation with 'level' ones
    if (!std::next_permutation(mask.begin(), mask.end())) {
        // No more at this level, try next level
        ++level;
        if (level > n) return false;
        init_level();
    }

    // Skip restricted masks
    while (std::any_of(restrictions.begin(), restrictions.end(),
                       [&](const std::vector<bool>& r) { return matches_restriction(mask, r); })) {
        if (!std::next_permutation(mask.begin(), mask.end())) {
            ++level;
            if (level > n) return false;
            init_level();
        }
    }

    return true;
}

