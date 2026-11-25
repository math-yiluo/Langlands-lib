# Algebraic and reductive group schemes: what Mathlib provides

The Library's group schemes are group objects in schemes over a base,
`Langlands.GroupScheme S := Grp (Over S)`, for an arbitrary base scheme `S`. This note lists what
Mathlib provides for them and for their root data, and names the Library modules that supply what
Mathlib lacks. Mathlib paths are relative to `Mathlib/`.

## Affine group schemes, Hopf algebras and group algebras

- `AlgebraicGeometry/Group/Affine.lean`: `bialgSpec : (CommBialgCat R)ᵒᵖ ⥤ Mon (Over (Spec R))`
  and `hopfSpec : (CommHopfAlgCat R)ᵒᵖ ⥤ Grp (Over (Spec R))`, both fully faithful
  (`bialgSpec.fullyFaithful`, `hopfSpec.fullyFaithful`). A commutative Hopf algebra over `R`
  therefore gives a group scheme in `GroupScheme (Spec R)`.
- `Algebra/Category/CommBialgCat.lean` and `Algebra/Category/CommHopfAlgCat.lean`: the categories
  of commutative bialgebras and of commutative Hopf algebras, and
  `commHopfAlgCatEquivCogrpCommAlgCat : CommHopfAlgCat R ≌ (Grp (CommAlgCat R)ᵒᵖ)ᵒᵖ`.
- `RingTheory/Bialgebra/MonoidAlgebra.lean`: the bialgebra structure on monoid algebras and on
  Laurent polynomials (`LaurentPolynomial.instBialgebra`, with
  `LaurentPolynomial.comul_T : comul (T n) = T n ⊗ₜ T n`); `MonoidAlgebra.mapDomainBialgHom`;
  `MonoidAlgebra.liftGroupLikeBialgHom : R[GroupLike R A] →ₐc[R] A`;
  `MonoidAlgebra.span_isGroupLikeElem`, which says that a group algebra is spanned by its
  group-like elements; `MonoidAlgebra.liftMulEquiv : (M →* A) ≃* WithConv (R[M] →ₐ[R] A)`, which
  classifies algebra maps out of a monoid algebra; and `AddMonoidAlgebra.toMultiplicativeBialgEquiv`.
  Over a domain `R`: `MonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one` (the group-like
  elements of `R[M]` are the `single m 1`) and, for groups `G` and `H`,
  `MonoidAlgebra.mapDomainBialgHomEquiv : (G →* H) ≃ (R[G] →ₐc[R] R[H])`, whose inverse is
  `MonoidAlgebra.mapDomainOfBialgHom`.
- `RingTheory/HopfAlgebra/MonoidAlgebra.lean`: the Hopf algebra structure on group algebras and on
  Laurent polynomials (`LaurentPolynomial.instHopfAlgebra`; for coefficients `R` itself this is
  the coordinate algebra of `𝔾ₘ` over `R`).
- `RingTheory/Coalgebra/GroupLike.lean`: `linearIndep_groupLikeVal`, the linear independence of
  group-like elements over a domain. `RingTheory/HopfAlgebra/GroupLike.lean`: the group
  `GroupLike R A` of group-like elements of a Hopf algebra `A`, commutative when `A` is
  (`GroupLike.instCommGroup`).
- `CategoryTheory/Monoidal/Cartesian/Over.lean`: the lemmas
  `CategoryTheory.Over.prodComparisonIso_pullback_*` on the product comparison of the pullback
  functor between over categories. `AlgebraicGeometry/Limits.lean`: `specULiftZIsTerminal`, which
  says that `Spec (ULift ℤ)` is terminal.
- Galois actions: `Field.absoluteGaloisGroup` (`FieldTheory/AbsoluteGaloisGroup.lean`) and
  `Rep.ofMulDistribMulAction` (`RepresentationTheory/Rep/Basic.lean`), the `ℤ`-linear
  representation on `Additive G` of a monoid acting on a commutative group `G` through a
  `MulDistribMulAction`.

Mathlib has no diagonalizable group schemes and no tori. The Library defines them on
`Langlands.GroupScheme`: `Diagonalizable.groupScheme` in
`Langlands/GroupScheme/Torus/Diagonalizable.lean`; `splitTorus` and `IsSplitTorus` in
`Langlands/GroupScheme/Torus/Split.lean`; over a base scheme, `RelativeMultiplicativeType.diagonalizable`,
`RelativeMultiplicativeType.IsDiagonalizable` and `RelativeMultiplicativeType.IsMultiplicativeType`
in `Langlands/GroupScheme/Torus/RelativeMultiplicativeType.lean`, and `RelativeTorus.IsTorus` in
`Langlands/GroupScheme/Torus/Relative.lean`.

## Root data and root systems

- `LinearAlgebra/RootSystem/Defs.lean`: `RootPairing ι R M N` and
  `RootDatum X₁ X₂ := RootPairing ι ℤ X₁ X₂`. Neither finiteness of the index type `ι` nor finite
  generation of `X₁` and `X₂` is part of the definition; they are separate hypotheses
  (`[Finite ι]`, `[Module.Finite ℤ X₁]`, `[Module.Finite ℤ X₂]`).
- In the same directory: `Base.lean` (`RootPairing.Base`), `WeylGroup.lean`
  (`RootPairing.weylGroup`, a subgroup of `RootPairing.Aut P`), `Hom.lean` (`RootPairing.Equiv`
  and `RootPairing.Aut`), `Reduced.lean`, and results for finite index types in `Finite/`.

The Library's root datum of a split maximal torus is a Mathlib root datum.
`Langlands.GroupScheme.IsRootDatumOf i P` (`Langlands/GroupScheme/Reductive/RootDatum.lean`), for a
commutative group scheme `T` and an affine group scheme `G` over a field `k`, a homomorphism
`i : T.toGrp ⟶ G` and `P : RootDatum J (characterLattice T) (cocharacterLattice T)`, says that the
pairing of `P` is `latticePairing T`, that its roots are the roots of `i`, and that each
reflection of `P` is induced by a point normalizing `i`. For a root datum `P` of the base change
of `i` to an extension `E` of `k`, each automorphism of `E` over `k` acts by an element of
`RootPairing.Aut P` (`IsRootDatumOf.galoisRootDatumAut`, in
`Langlands/GroupScheme/Reductive/RootDatumGaloisCoroots.lean`).

`Algebra/Lie/Weights/RootSystem.lean` has
`LieAlgebra.IsKilling.rootSystem H : RootPairing H.root K (Dual K H) H`, the root system of a
finite-dimensional Lie algebra `L` with nondegenerate Killing form over a field `K` of
characteristic zero, relative to a splitting Cartan subalgebra `H`
(`[H.IsCartanSubalgebra] [IsTriangularizable K H L]`; Cartan subalgebras are defined in
`Algebra/Lie/CartanSubalgebra.lean`), with `IsCrystallographic` and `IsReduced` instances. It
needs characteristic zero and a nondegenerate Killing form, so it does not apply in positive
characteristic or to a reductive group with a nontrivial central torus, and its coefficients lie
in `K` and are attached to the Lie algebra rather than to the character lattice of a torus. The
Library does not use it.
