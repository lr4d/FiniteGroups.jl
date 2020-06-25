
"
    Iterating over an AbstractGroup is the same as iterating over the set.
"
abstract type AbstractGroup end

# TODO: convert `Set` to `AbstractSet` where possible to support OrderedSets et al
"""
    Stucture consisting of a set and a binary operation. No constraints are put on either expression.
"""
struct Groupoid{T} <: AbstractGroup
    set::Set{T}
    operation::Function
end

"""
    Group.
    The following axioms must hold. Assuming a group G = (S, ∘), then
      - Closure: the group must be closed under the binary operation.
        ∀x,y ∈ S: x ∘ y ∈ S
      - Associativity:
        ∀x,y,z ∈ S: x ∘ (y ∘ z) =  (x ∘ y) ∘ z
      - Identity:
        ∃e ∈ S: ∀x ∈ S, x ∘ e = x = e ∘ x
      - Inverses:
        ∀x ∈ S, ∃ x⁻¹ ∈ S : x ∘ x⁻¹ = e = x⁻¹ ∘ x
"""
struct Group{T} <: AbstractGroup where {T}
    set::Set{T}
    operation::Function
    Group{T}(set, operation) where T = if _validate_group(Groupoid(set, operation)) new(set, operation) end
end
Group(set::Set{T}, operation::Function) where {T} = Group{T}(set, operation)

"""
    Subgroup of a group.
    Create using SubGroup(group, subset).
    Must be closed under the group operation, include the identity element and include inverses for each element.
"""
struct SubGroup{T} <: AbstractGroup where {T}
    group::Group{T}
    set::Set{T}
    operation::Function
end

function SubGroup(group::Group{T}, subset::Set{<:T})::SubGroup{T} where {T}
    @assert subset ⊆ group.set
    g = Groupoid(subset, group.operation)
    assert_closure(g)
    _assert_inverses(get_identity_element(g), g.set, g.operation)
    return SubGroup(group, subset, group.operation)
end

abstract type AbstractGroupAction end

struct _GroupActionLike{T} <: AbstractGroupAction where {T}
    group::Group{<:T}
    set::Set{<:T}
    action::Function
end

struct GroupAction{T} <: AbstractGroupAction where {T}
    group::Group{<:T}
    set::Set{<:T}
    action::Function
    #GroupAction{T}
end


# TODO: fix convert below, then simplify code as necessary
# import Base: convert
# convert(T::Set{S}, x::Array{S, 1}) where {S} = T(_ for _ in x)
# convert(Set, Array{Int, 1}([1]))
function coset(left::T, set::Set{T}, operation::Function)::Set{T} where {T}
    #Set(x for x in operation.(left, set))
    Set(operation(left, right) for right in set)
end

function coset(set::Set{T}, right::T, operation::Function)::Set{T} where {T}
#    Set(x for x in operation.(set, right))
    Set(operation(left, right) for left in set)

end

function coset(left, group::AbstractGroup)
    coset(left, group.set, group.operation)
end

function coset(group::AbstractGroup, right)
    coset(group.set, right, group.operation)
end


function set_composition(left_set::Set{<:T}, right_set::Set{<:T}, operation::Function)::Set  where {T}
    # `map` is not defined on sets
    # reduce(union, coset(left, right_set, operation) for left in left_set)
    Set(operation(left, right) for left in left_set for right in right_set)
end


function assert_closure(set::Set, closed_in_set::Set, operation::Function)::Nothing
    # We only check left closure.
    @assert set_composition(set, closed_in_set, operation) ⊆ closed_in_set
end

function assert_closure(group::AbstractGroup)::Nothing
    assert_closure(group.set, group.set, group.operation)
end

function assert_closure(ga::AbstractGroupAction)::Nothing
    assert_closure(ga.group.set, ga.set, ga.action)
end

function assert_associativity(set::Set, operation::Function)::Nothing
    for x in set
        for y in set
            for z in set
                a = operation(x, operation(y, z))
                b = operation(operation(x, y), z)
                @assert a == b "$x ∘ ($y ∘ $z) = $a ≠ $b = ($x ∘ $y) ∘ $z"
            end
        end
    end
end

function assert_associativity(group::AbstractGroup)::Nothing
    assert_associativity(group.set, group.operation)
end
function _assert_identity_element(element::T, set::Set{T}, operation::Function)::Nothing where {T}
    # we assume broadcasting works on the operation
    # @assert operation.(element, set) == set  # should be using ordered sets or vectors here
    for x in set
         @assert x == operation(element, x) == operation(x, element)
    end
end

function get_identity_element(group::AbstractGroup) # TODO: return type
    for x in group.set
        try
            _assert_identity_element(x, group.set, group.operation)
            return x
        catch AssertionError
            continue
        end
    end
    throw(AssertionError("No identity element found"))
end

function _assert_inverses(identity_element::T, set::Set{T}, operation::Function)::Nothing where {T}
    for item in set
        @assert identity_element in coset(item, set, operation)
        @assert identity_element in coset(set, item, operation)
    end
end

function _validate_group(group::AbstractGroup)::Bool
    # Validation
    assert_closure(group)
    assert_associativity(group)
    e = get_identity_element(group)  # This raises on failure
    _assert_inverses(e, group.set, group.operation)
    return true
end

function naive_isequal(x::T, y::T) where T
    for f in fieldnames(T)
        if getfield(x, f) != getfield(y, f)
            return false
        end
    end
    return true
end

import Base: ==
==(x::T, y::T) where T<:AbstractGroup = naive_isequal(x, y)
# ==(x::Group, y::Group) = naive_isequal(x, y)
# ==(x::SubGroup, y::SubGroup) = naive_isequal(x, y)
function ==(x::AbstractGroup, y::SubGroup)::Bool
    if y.set == x.set && x.operation == y.operation
        return true
    end
    return false
end
==(x::SubGroup, y::AbstractGroup) = ==(y, x)
# Prevent `MethodError: ==(::SubGroup{Int64}, ::SubGroup{Int64}) is ambiguous`
==(x::SubGroup, y::SubGroup) = naive_isequal(x, y)

import Base: iterate
iterate(group::AbstractGroup) = iterate(group.set)
iterate(group::AbstractGroup, t::T) where {T} = iterate(group.set, t)
import Base: length
length(x::AbstractGroup) = length(x.set)


"""
    N is a _normal_ subgroup of G if ∀g ∈ G, gN = Ng
    N is a normal subgroup of G iff N is a subgroup of G and N is a union of conjugacy classes of G
"""
function isnormal(subgroup::SubGroup)
    for g in subgroup.group
        left_coset = coset(g, subgroup)
        right_coset = coset(subgroup, g)
        if coset(g, subgroup) != coset(subgroup, g)
            return false
        end
    end
    return true
end

function iscyclic(group::AbstractGroup)
    if length(find_generators(group)) > 0
        return true
    end
    return false
end

function quotient_group(subgroup::SubGroup)
    @assert isnormal(subgroup) "Subgroup must be normal"
    # The set here is equal to the "partition" of the group into cosets created by group elements with the subgroup
    f(x::Set, y::Set) = set_composition(x, y, subgroup.operation)
    return Group(Set(coset(g, subgroup) for g in subgroup.group), f)
end



function generate_subgroup(group::AbstractGroup, generator)::SubGroup
    e = get_identity_element(group)
    generated_set = Set([e generator])
    p = group.operation(generator, generator)
    while p != e
        push!(generated_set, p)
        p = group.operation(p, generator)
    end
    SubGroup(group, generated_set, group.operation)
end

function find_generators(group::AbstractGroup)::Set
    filter(g->generate_subgroup(group, g) == group, group.set)
end

function _cayley_table(group::AbstractGroup) # TODO: move to utils
    elements = [x for x in group.set]
    inside = map(x->
            map(y->group.operation(x, y),
            elements
            ), elements)

    return elements, inside
end
# _cayley_table((generate_subgroup(G, 6) |> quotient_group))[2]


"""

Conjugate x by g, i.e. perform gxg⁻¹

"""
function conjugate(group::AbstractGroup, x::T, g::T) where {T}
    group.operation(group.operation(g, x), inv(group, g))
end

"""
Return { gxg⁻¹: ∀g ∈ G}
"""
function conjugacy_class(group::AbstractGroup, x)::Set
    Set(conjugate(group, x, g) for g in group)
end

"""
Return the distinct conjugacy classes in `group`.
The set of distinct conjugacy classes forms a partition of the group.
"""
function conjugacy_classes(group::AbstractGroup)::Set
    Set(conjugacy_class(group, x) for x in group)
end

"""
Obtain the inverse of `x` in `group`.
"""
function inv(group::AbstractGroup, x)
    e = get_identity_element(group)
    for h in group
        if group.operation(x, h) == group.operation(h, x) == e
            return h
        end
    end
    return missing  # TODO: missing or nothing?
end

abstract type AbstractHomomorphism end
"""
An isomorphism ϕ: (G, ∘) → (H, ⋆) is a mapping which satisfies the following properties
- ϕ is one-to-one and onto

See also: Homomorphism
"""
struct Isomorphism <: AbstractHomomorphism
    from_group::AbstractGroup
    to_group::AbstractGroup
    mapping::Dict
end

"""
An isomorphism ϕ: (G, ∘) → (H, ⋆) is a mapping which satisfies the following property:
    ∀x,y ∈ G, ϕ(x ∘ y) = ϕ(x) ⋆ ϕ(y)   (i.e. it preserves composites)
"""
struct Homomorphism <: AbstractHomomorphism
    from_group::AbstractGroup
    to_group::AbstractGroup
    mapping::Dict
end


function order(group::AbstractGroup)
    return length(group.set)
end

function order(group::AbstractGroup, x)
    return length(generate_subgroup(group, x))
end

function get_isomorphism(a::AbstractGroup, b::AbstractGroup)
    if a == b  # Automorphism
         return Dict(k=>k for k in a)
    end
    if iscyclic(a) && iscyclic(b) && order(a) == order(b)  # Cyclic subgroups of the same order
        gen_a, gen_b = find_generators(a) |> first, find_generators(b) |> first
        mapping = Dict(gen_a => gen_b)
        p_a = gen_a
        p_b = gen_b
        for i in 1:order(a)
            p_a = a.operation(p_a, gen_a)
            p_b = b.operation(p_b, gen_b)
            mapping[p_a] = p_b
        end
        return mapping
    end
    throw("Not implemented")
end

"""
Assert the following property, where mapping=ϕ, from=(G, ∘), to=(H, ⋆)
    ∀ x,y ∈ G; ϕ(x, y) = ϕ(x) ⋆ ϕ(y)
"""
function _assert_homomorphism_property(mapping::Dict, from::AbstractGroup, to::AbstractGroup)
   for x in from
        for y in from
            @assert mapping[from.operation(x, y)] == to.operation(mapping[x], mapping[y])
        end
    end
end

"""
Let (G, ∘) be a group, X be a set and ^ be a group action.
    ∀ g,h ∈ G; ∀x in X; g ^ (h ^ x) = (g ∘ h) ^ x
"""
function _assert_homomorphism_property(ga::AbstractGroupAction)
    for g in ga.group
        for h in ga.group
            for x in ga.set
                @assert ga.action(g, ga.action(h, x)) == ga.action(ga.group.operation(g, h), x)
            end
        end
    end
end

function _transform(ϕ::Function, arr::Union{Vector, AbstractSet})::Union{Vector, AbstractSet}
    return ϕ.(arr)
end

function _transform(ϕ::Dict, arr::Union{Vector, AbstractSet})::Union{Vector, AbstractSet}
    return _transform(x-> ϕ[x], arr)
end

"""
Let G be a group and ϕ: G → H be a homomorphism. Then,
    Ker ϕ = {g ∈ G: ϕ(g) = e_H}

Let V, W be vector subspaces and t: V → W be a linear transfomation. Then,
    Ker t = {v⃗ ∈ V: ϕ(v⃗) = 0⃗}
"""
function kernel(transformation::Union{Function, Dict}, from::Union{AbstractSet, AbstractGroup}, identity)
    v = [g for g in from]
    t = _transform(transformation, v)
    mask = t .== identity
    return Set(v[mask])
end

function image(transformation, from::AbstractSet)::Set
   _transform(transformation, from) |> Set
end
function image(transformation, from::AbstractGroup)::Set
   _transform(transformation, from.set) |> Set
end


function GroupAction(group::Group{<:T}, set::Set{<:T}, action::Function)::GroupAction{T} where {T}
    ga = _GroupActionLike(group, set, action)
    assert_closure(ga)

    e = get_identity_element(ga.group)
    for x in ga.set
        @assert ga.action(e, x) == x
    end

    _assert_homomorphism_property(ga)

    return GroupAction{T}(group, set, action)
end

"""
    Orb x = {∀g ∈ G, g ^ x}
"""
function orbit(ga::AbstractGroupAction, x)::Set  # TODO: define type
    @assert x in ga.set
    return ga.action.(ga.group, x) |> Set
end

"""
    Get the set of all orbits for the group action
"""
function orbits(ga::AbstractGroupAction)::Set
    return Set(orbit(ga, x) for x in ga.set)
end


"""
    Stab x = {g ∈ G: g^x = x}
"""
function stabilizer(ga::AbstractGroupAction, x)
    @assert x in ga.set
    v = [g for g in ga.group.set]
    t = ga.action.(v, x)
    stable_mask = t .== x
    return Set(v[stable_mask])
end

# function stabilizers(ga::AbstractGroupAction)
#     return Set(stabilizer(ga, x) for x in ga.set)
# end

"""
    Fix g = {x ∈ X: g^x = x}
"""
function fixed_set(ga::AbstractGroupAction, g)
    @assert g in ga.group.set
    v = [x for x in ga.set]
    t = ga.action.(g, v)
    return Set(v[t .== v])
end
