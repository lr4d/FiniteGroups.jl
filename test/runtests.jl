using Test

include("../src/FiniteGroups.jl")

@testset "coset" begin
    @test coset(1, Set([1, 2, 3]), *) == Set([1, 2, 3])
    @test coset(0, Set([-1, 3, 4, 5]), *) == Set([0])
    # @test coset(Set([1]), Set([Set([1 2]), Set([1, 3])]), ((x, y)->coset(x, y, +))) == Set([Set([2, 4]), Set([2, 3])])

end

@testset "set composition" begin
    @test set_composition(Set([1]), Set([1, 2]), (+)) == Set([2, 3])
end

@testset  "validate group" begin
    G = Group(Set([1, 2]), (x, y)-> x * y % 3)
    @test_throws AssertionError Group(Set([-1, 1]), (+))
end

@testset  "coset{group}" begin
    G = Group(Set([1, 2]), (x, y)-> x * y % 3)
    @test coset(0, G) == Set([0])
    @test coset(2, G) == Set([1, 2])
end

@testset "naive_isequal" begin
    add_mod_2(x, y) = (x + y) % 2
    mod_3(x, y) = mod(x*y, 3)

    G = Group(Set([0, 1]), add_mod_2)
    @test naive_isequal(G, Group(Set([0]), add_mod_2)) == false
    @test naive_isequal(G, G)
    @test_throws MethodError naive_isequal(G, SubGroup(G, Set([1]), mod_3))
end


@testset  "subgroup definition" begin
    mod_3(x, y) = mod(x*y, 3)
    G = Group(Set([1, 2]), mod_3)
    @test SubGroup(G, Set([1])) == SubGroup(G, Set([1]), mod_3)
    @test G == SubGroup(G, G.set)
    @test SubGroup(G, G.set) == G
    @test SubGroup(G, Set([1])) != G
end

@testset "normal subgroup" begin
    # In a cyclic group, all subgroups are normal
    ×₇(x, y) = mod(x * y, 7)
    G = Group(Set([1 2 3 4 5 6]), ×₇)
    N = SubGroup(G, Set([1 6]))
    @test isnormal(N)
    @test isnormal(SubGroup(G, G.set))
    @test isnormal(SubGroup(G, Set([1])))
    @test inv(G, 2) == 4
    @test conjugate(G, 2, 4) == 2
    # Symmetry group of triangle
    mapping = Dict( # Non-commutative for `:r`, `:s`, `:t`
        :e => Dict(:e => :e, :a => :a, :b => :b, :t => :t, :r => :r, :s => :s),
        :a => Dict(:e => :a, :a => :b, :b => :e, :t => :s, :r => :t, :s => :r),
        :b => Dict(:e => :b, :a => :e, :b => :a, :t => :r, :r => :s, :s => :t),
        :r => Dict(:e => :r, :a => :s, :b => :t, :t => :b, :r => :e, :s => :a),
        :s => Dict(:e => :s, :a => :t, :b => :r, :t => :a, :r => :b, :s => :e),
        :t => Dict(:e => :t, :a => :r, :b => :s,:t => :e, :r => :a, :s => :b),

    )

    f(x, y) = mapping[x][y]
    G = Group(Set([:e :a :b :r :s :t]), f)
    S = SubGroup(G, Set([:e :r]))
    @test isnormal(S) == false
end


@testset "conjugacy classes" begin

    mapping = Dict( # Non-commutative for `:r`, `:s`, `:t`
    :e => Dict(:e => :e, :a => :a, :b => :b, :t => :t, :r => :r, :s => :s),
    :a => Dict(:e => :a, :a => :b, :b => :e, :t => :s, :r => :t, :s => :r),
    :b => Dict(:e => :b, :a => :e, :b => :a, :t => :r, :r => :s, :s => :t),
    :r => Dict(:e => :r, :a => :s, :b => :t, :t => :b, :r => :e, :s => :a),
    :s => Dict(:e => :s, :a => :t, :b => :r, :t => :a, :r => :b, :s => :e),
    :t => Dict(:e => :t, :a => :r, :b => :s,:t => :e, :r => :a, :s => :b),

    )
    f(x, y) = mapping[x][y]
    G = Group(Set([:e :a :b :r :s :t]), f)

    @test conjugacy_class(G, :t) == conjugacy_class(G, :s) == conjugacy_class(G, :r) == Set([:s :r :t])
    @test conjugacy_class(G, :a) == Set([:a :b])
    @test conjugacy_classes(G) == Set([Set([:a :b]), Set([:s :r :t]), Set([:e])])

end



@testset "order" begin
    ×₇(x, y) = mod(x * y, 7)
    G = Group(Set([1 2 3 4 5 6]), ×₇)
    @test order(G) == 6
    @test order(G, 1) == 1
    @test order(G, 2) == 3
end


@testset "generators" begin
    ×₇(x, y) = mod(x * y, 7)
    G = Group(Set([1 2 3 4 5 6]), ×₇)
    N = SubGroup(G, Set([1 6]))
    @test generate_subgroup(G, 6) == N
    @test generate_subgroup(G, 1) == SubGroup(G, Set([1]))
    @test generate_subgroup(G, 3) == G
    @test find_generators(G) == Set([3 5])
    @test iscyclic(G)

    mapping = Dict( # Non-commutative for `:r`, `:s`, `:t`
    :e => Dict(:e => :e, :a => :a, :b => :b, :t => :t, :r => :r, :s => :s),
    :a => Dict(:e => :a, :a => :b, :b => :e, :t => :s, :r => :t, :s => :r),
    :b => Dict(:e => :b, :a => :e, :b => :a, :t => :r, :r => :s, :s => :t),
    :r => Dict(:e => :r, :a => :s, :b => :t, :t => :b, :r => :e, :s => :a),
    :s => Dict(:e => :s, :a => :t, :b => :r, :t => :a, :r => :b, :s => :e),
    :t => Dict(:e => :t, :a => :r, :b => :s,:t => :e, :r => :a, :s => :b),

)
    f(x, y) = mapping[x][y]
    G = Group(Set([:e :a :b :r :s :t]), f)
    @test find_generators(G) == Set([])
    @test iscyclic(G) == false
end


@testset "ismorphism" begin
    U12 = Group(Set([1 5 7 11]), (x, y)->mod(x*y, 12))
    mapping = Dict(
        :e => Dict(:e=>:e, :a=>:a, :r=>:r, :s=>:s),
        :a => Dict(:e=>:a, :a=>:e, :r=>:s, :s=>:r),
        :r => Dict(:e=>:r, :a=>:s, :r=>:e, :s=>:a),
        :s => Dict(:e =>:s, :a=>:r, :r=>:a, :s=>:e)
    )
    f(x, y) = mapping[x][y]
    S_rectangle = Group(keys(mapping) |> Set, f)

    trivial_homomorphism = Dict(k => :e for k in U12)
    _assert_homomorphism_property(trivial_homomorphism, U12, S_rectangle)

    # Automorphism
    @test get_isomorphism(S_rectangle, S_rectangle) == Dict(:e=>:e, :a=>:a, :r=>:r, :s=>:s)

    # Kernel, image
    @test image(trivial_homomorphism, U12) == Set([:e])
end

@testset "group actions" begin
    U12 = Group(Set([1 5 7 11]), (x, y)->mod(x*y, 12))
    GA = GroupAction(U12, Set(1:3), (x,y) -> mod(x*y, 4))  # 4 is a divisor of 12, so will be preserving composites
    @test orbit(GA, 1) == Set([1 3])
    @test orbits(GA) == Set([Set([1, 3]), Set([2])])
    @test stabilizer(GA, 1) == Set([1 5])
    @test fixed_set(GA, 1) == Set(1:3)
    @test fixed_set(GA, 11) == Set([2])
end


