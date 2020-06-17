Create mathematical groups in Julia.

# Example Usage
```julia
using FiniteGroups

# Define a group
×₇(x, y) = mod(x * y, 7)
G = Group(Set([1 2 3 4 5 6]), ×₇)

# Create a subgroup
N = SubGroup(G, Set([1 6]))

# In a cyclic group, all subgroups are normal
@assert iscyclic(G)
@assert isnormal(N)

# Cyclic groups: find group generators
find_generators(G)

# Cyclic groups: isomorphisms
×₁₇(x, y) = mod(x * y, 17)
G_1 = Group(Set([1 4 13 16]), ×₁₇)
+₁₆(x, y) = mod(x + y, 16)
G_2 = Group(Set([0 4 8 12]), +₁₆)
get_isomorphism(G_1, G_2)

# Quotient groups
+₆(x, y) = mod(x+y, 6)
Z₆ = 0:5 |> Set
G = Group(Z₆, +₆)  # Verify that it is a group

ϕ(n::Int) = mod(3^n, 4)
Ker = kernel(ϕ, Z₆, 1)
Q = quotient_group(SubGroup(G, Ker))

# Group actions
U12 = Group(Set([1 5 7 11]), (x, y)->mod(x*y, 12))
GA = GroupAction(U12, Set(1:3), (x,y) -> mod(x*y, 4))  # 4 is a divisor of 12, so will be preserving composites
orbit(GA, 1) # Get orbit of group action for 1
orbits(GA)  # Get set of all orbits
stabilizer(GA, 1)
fixed_set(GA, 11)
```
# Intention
This package is not optimized for fast computational performance, it rather focuses on mathematical correctness.

