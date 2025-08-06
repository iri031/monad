#include <gtest/gtest.h>

#include <category/core/hex_literal.hpp>
#include <category/mpt2/child_data.hpp>
#include <category/mpt2/compute.hpp>
#include <category/mpt2/node.hpp>
#include <category/mpt2/util.hpp>

using namespace MONAD_MPT2_NAMESPACE;
using namespace monad::literals;

struct DummyCompute final : Compute
{
    // hash length = 1
    virtual unsigned compute_len(
        std::span<ChildData> const children, uint16_t const, NibblesView const,
        std::optional<monad::byte_string_view> const value) override
    {
        if (!value.has_value()) {
            return 0;
        }
        unsigned len = 0;
        for (auto const &i : children) {
            len += i.data_size;
        }
        return len >= 32 ? 32 : len;
    }

    virtual unsigned compute_branch(unsigned char *, Node *) override
    {
        return 0;
    }

    virtual unsigned compute(unsigned char *buffer, Node *) override
    {
        buffer[0] = 0xa;
        return 1;
    }
};

auto const value = 0x12345678_hex;
auto const path = 0xabcdabcdabcdabcd_hex;

TEST(NodeTest, leaf)
{
    NibblesView const path1{1, 10, path.data()};
    Node::UniquePtr node{make_node(0, {}, path1, value, {}, 0)};

    EXPECT_EQ(node->mask, 0);
    EXPECT_EQ(node->value(), value);
    EXPECT_EQ(node->path_nibble_view(), path1);
    EXPECT_EQ(node->get_allocate_size(), 29);
}

TEST(NodeTest, leaf_single_branch)
{
    DummyCompute comp{};
    NibblesView const path1{12, 16, path.data()};

    ChildData children[1];
    children[0].data_size = 1;
    children[0].data[0] = 0xa;
    children[0].branch = 0xc;
    children[0].node = make_node(0, {}, path1, value, {}, 0);
    NibblesView const path2{1, 10, path.data()};
    uint16_t const mask = 1u << 0xc;
    Node::UniquePtr node{
        create_node_with_children(comp, mask, children, path2, value, 0)};

    EXPECT_EQ(node->value(), value);
    EXPECT_EQ(node->path_nibble_view(), path2);
    EXPECT_EQ(node->bitpacked.data_len, 1);
    EXPECT_EQ(node->get_allocate_size(), 57);
}

TEST(NodeTest, leaf_multiple_branches)
{
    DummyCompute comp{};
    NibblesView const path1{12, 16, path.data()};

    ChildData children[2] = {
        ChildData{.data_size = 1}, ChildData{.data_size = 1}};
    children[0].data[0] = 0xa;
    children[1].data[0] = 0xa;
    children[0].branch = 0xa;
    children[1].branch = 0xc;
    children[0].node = make_node(0, {}, path1, value, {}, 0);
    children[1].node = make_node(0, {}, path1, value, {}, 0);

    NibblesView const path2{1, 10, path.data()};
    uint16_t const mask = (1u << 0xa) | (1u << 0xc);
    Node::UniquePtr node{
        create_node_with_children(comp, mask, children, path2, value, 0)};

    EXPECT_EQ(node->value(), value);
    EXPECT_EQ(node->path_nibble_view(), path2);
    EXPECT_EQ(node->bitpacked.data_len, 2);
    EXPECT_EQ(node->get_allocate_size(), 85);
}

TEST(NodeTest, branch_node)
{
    DummyCompute comp{};
    NibblesView const path1{12, 16, path.data()};

    ChildData children[2] = {
        ChildData{.data_size = 1}, ChildData{.data_size = 1}};
    children[0].data[0] = 0xa;
    children[1].data[0] = 0xa;
    children[0].branch = 0xa;
    children[1].branch = 0xc;
    children[0].node = make_node(0, {}, path1, value, {}, 0);
    children[1].node = make_node(0, {}, path1, value, {}, 0);

    NibblesView const path2{1, 1, path.data()}; // path2 is empty
    uint16_t const mask = (1u << 0xa) | (1u << 0xc);
    Node::UniquePtr node{create_node_with_children(
        comp, mask, children, path2, std::nullopt, 0)};

    EXPECT_EQ(node->value_len, 0);
    EXPECT_EQ(node->bitpacked.data_len, 0);
    EXPECT_EQ(node->path_nibble_view(), path2);
    EXPECT_EQ(node->get_allocate_size(), 74);
}

TEST(NodeTest, extension_node)
{
    DummyCompute comp{};
    NibblesView const path1{12, 16, path.data()};

    ChildData children[2] = {
        ChildData{.data_size = 1}, ChildData{.data_size = 1}};
    children[0].data[0] = 0xa;
    children[1].data[0] = 0xa;
    children[0].branch = 0xa;
    children[1].branch = 0xc;
    children[0].node = make_node(0, {}, path1, value, {}, 0);
    children[1].node = make_node(0, {}, path1, value, {}, 0);

    NibblesView const path2{1, 10, path.data()};
    uint16_t const mask = (1u << 0xa) | (1u << 0xc);
    Node::UniquePtr node{create_node_with_children(
        comp, mask, children, path2, std::nullopt, 0)};

    EXPECT_EQ(node->value_len, 0);
    EXPECT_EQ(node->path_nibble_view(), path2);
    EXPECT_EQ(node->bitpacked.data_len, 0);
    EXPECT_EQ(node->get_allocate_size(), 79);
}

TEST(NodeTest, super_large_node)
{
    DummyCompute const comp{};
    size_t const value_len = 255 * 1024 * 1024;
    monad::byte_string value(value_len, 0);
    Node::UniquePtr node{make_node(0, {}, {}, value, {}, 0)};
    EXPECT_EQ(node->value_len, value_len);
    EXPECT_EQ(node->bitpacked.data_len, 0);
    EXPECT_EQ(
        node->get_allocate_size(),
        value_len + sizeof(Node) + Node::disk_size_bytes);
}
