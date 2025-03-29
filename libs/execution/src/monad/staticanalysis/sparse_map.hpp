#include <algorithm> // For std::fill_n
#include <cstdint>   // For uint16_t, int16_t
#include <limits>    // Add this for std::numeric_limits
#include <stdexcept>  // For std::out_of_range
#include <cassert>    // For assert

template<typename T, uint16_t MAX_KEY, uint16_t MAX_ENTRIES>
class SparseMap {
public:
    // Constructor
    SparseMap() : size_(0) {
        // Initialize key-to-index mapping array to UINT16_MAX (indicates empty)
        std::fill_n(key_to_index_, MAX_KEY, std::numeric_limits<uint16_t>::max());
    }

    // Insert a key-value pair into the map
    bool insert(uint16_t key, const T& value) {
        if (key >= MAX_KEY)
            return false; // Key out of bounds

        uint16_t index = key_to_index_[key];
        if (index != std::numeric_limits<uint16_t>::max()) {
            // Key already exists; update the value
            values_[index] = value;
            return true;
        }

        if (size_ >= MAX_ENTRIES) {
            std::cerr << "overflow. current SparseMap items: " << std::endl;
            uint64_t num_items = 0;
            for (uint16_t i = 0; i < MAX_KEY; i++) {
                if (key_to_index_[i] != std::numeric_limits<uint16_t>::max()) {
//                    std::cerr << i << "(" << key_to_index_[i] << ")" << ",";
                    std::cerr << i << ",";
                    num_items++;
                }
            }
            std::cerr << std::endl;
            std::cerr << "num_items: " << num_items << std::endl;
            std::terminate();
        }

        // Insert new key-value pair
        key_to_index_[key] = size_;
        values_[size_] = value;
        ++size_;
        return true;
    }

    // Retrieve a reference to the value associated with a key
    T& get(uint16_t key) {
        assert(key < MAX_KEY && key_to_index_[key] != std::numeric_limits<uint16_t>::max() && 
               "Key not found in SparseMap");
        return values_[key_to_index_[key]];
    }

    // Retrieve a const reference to the value associated with a key
    const T& get(uint16_t key) const {
        assert(key < MAX_KEY && key_to_index_[key] != std::numeric_limits<uint16_t>::max() && 
               "Key not found in SparseMap");
        return values_[key_to_index_[key]];
    }

    // Clear the map
    void clear() {
        // Reset key-to-index mapping and size
        std::fill_n(key_to_index_, MAX_KEY, std::numeric_limits<uint16_t>::max());
        size_ = 0;
    }

    // Get the current size of the map
    uint16_t size() const {
        return size_;
    }

    // Check if a key exists in the map
    bool exists(uint16_t key) const {
        return key < MAX_KEY && key_to_index_[key] != std::numeric_limits<uint16_t>::max();
    }

    // Iterator class definition
    class iterator {
    public:
        iterator(const SparseMap* map, uint16_t current_key) 
            : map_(map), current_key_(current_key) {
            // Find first valid entry if we're not at the end
            if (current_key_ < MAX_KEY && !map_->exists(current_key_)) {
                operator++();
            }
        }

        iterator& operator++() {
            // Find next valid entry
            do {
                ++current_key_;
            } while (current_key_ < MAX_KEY && !map_->exists(current_key_));
            return *this;
        }

        bool operator!=(const iterator& other) const {
            return current_key_ != other.current_key_;
        }

        std::pair<uint16_t, const T&> operator*() const {
            return {current_key_, map_->get(current_key_)};
        }

    private:
        const SparseMap* map_;
        uint16_t current_key_;
    };

    // Iterator methods
    iterator begin() const {
        return iterator(this, 0);
    }

    iterator end() const {
        return iterator(this, MAX_KEY);
    }

private:
    uint16_t key_to_index_[MAX_KEY]; // Changed from int16_t to uint16_t
    T values_[MAX_ENTRIES];         // Pre-allocated array to store values
    uint16_t size_;                 // Current number of entries in the map
};
