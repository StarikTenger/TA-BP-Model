#pragma once

#include <cstdlib>
#include <vector>

int random_int(int min, int max);

bool next_mask(std::vector<bool>& mask);

class MaskGenerator {
public:
    MaskGenerator(int size);

    void restrict(const std::vector<bool>& restriction);
    void restrict_last();
    
    std::vector<bool>& get_mask() const;

    bool next();
private:
    std::vector<bool> mask;
    std::vector<bool> restriction;
    std::vector<bool> pending_restriction; 
    int level = 1;

    // Auxiliary fields for enumeration
    std::vector<bool> aux_mask;
    int free_count = 0;
    bool first = true;
    void update_aux();
    bool next_aux();
    void map_aux_to_mask();
};