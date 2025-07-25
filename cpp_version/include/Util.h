#pragma once

#include <cstdlib>
#include <vector>

int random_int(int min, int max);

bool next_mask(std::vector<bool>& mask);

/*
 * Bit mask generator used for ??? //TODO
 */
class MaskGenerator {
public:
    MaskGenerator(int size);

    void restrict(const std::vector<bool>& restriction);
    void restrict_last();
    
    std::vector<bool>& get_mask() const;

    bool next();
private:
    std::vector<bool> mask;
    std::vector<std::vector<bool>> restrictions;
    int level = 1;
    bool first = true;

    void init_level(); // helper to initialize mask for current level
};

// RandomBox inherits from std::vector and adds a method to pick a random element
template <typename T>
class RandomBox : public std::vector<T> {
public:
    using std::vector<T>::vector;

    T random_element() const {
        return (*this)[random_int(0, this->size() - 1)];
    }

    RandomBox<T>& operator=(const T& value) {
        this->clear();
        this->push_back(value);
        return *this;
    }
};

