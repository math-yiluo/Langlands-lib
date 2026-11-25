/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericDivisorGenericPoint
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorIntegral
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorLisse

/-!

# Generic vanishing for lisse generators: reduction to the codimension-one core

Let `X` be normal, `Z = V(h)` a principal divisor, `ζ` a generic point of `Z`, and `Rg_! Rj'_! M` a
lisse generator of `Dᵇc(X ∖ Z)` whose support has closure containing `ζ`. The local ring of `X` at
`ζ` is a discrete valuation ring, so the only proper generization of `ζ` is the generic point of
`X` (`AlgebraicGeometry.Scheme.specializes_eq_or_eq_genericPoint`); a set closed in `X ∖ Z` whose
closure contains `ζ` therefore contains the generic point of `X`
(`ProEtale.CondensedRing.genericPoint_mem_of_mem_closure`). Hence either `U₀ = ∅`, where everything
vanishes, or `U₀` covers `V ∖ Z` for an open neighbourhood `V` of `ζ`
(`ProEtale.CondensedRing.isEmpty_or_exists_opens_subset_range`). This proves the case of
generators whose support closure contains `ζ` from the codimension-one core
`ProEtale.CondensedRing.exists_isZero_upperStar_nearbyCycles_lowerShriek_of_subset_range`.

The core holds for every bounded constructible complex on `X ∖ Z`
(`ProEtale.CondensedRing.exists_isZero_upperStar_nearbyCycles_lowerShriek_padicAlgCl`): an
integral model and derived Nakayama reduce it to `𝔽_E`-coefficients.

## The finite-coefficient input

The core depends on the finite-coefficient statement
`ProEtale.CondensedRing.exists_isZero_upperStar_nearbyCycles_lowerShriek_residueField`
(`WeilConjectures.TraceFormula.Specialization.GenericDivisorResidue`): the local acyclicity along a
divisor of extensions by zero of constructible `𝔽_E`-complexes on the complement (the nearby cycles
of the deformation `x = t u` at the zero section).

-/

@[expose] public section

universe u

open CategoryTheory Limits Topology TopologicalSpace IsLocalRing Pretriangulated ZeroObject

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom]

/-! ### Sheaf-theoretic part of route (a) -/

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (k' : Type u) [Field k'] [Algebra k k'] [IsSeparated X.hom]

/-- **Empty support**: if the open `U₀` carrying the lisse sheaf `M` is empty, the lisse generator
`Rg_! Rj'_! M` vanishes, and so does the restricted specialization of its extension by zero. -/
theorem exists_isZero_upperStar_nearbyCycles_lowerShriek_of_isEmpty
    {I : X.left.IdealSheafData}
    {Z₀ : Over (Spec (.of k))} [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [IsSeparated Z₀.hom] (g : Z₀ ⟶ overRestrict X I.support.compl) [IsClosedImmersion g.left]
    {U₀ : Over (Spec (.of k))} [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom] (j' : U₀ ⟶ Z₀) [IsOpenImmersion j'.left] [IsEmpty U₀.left]
    (M : Dᵇc(U₀.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (e : N ≅ (boundedConstructibleLowerShriek ℓ g).obj
      ((boundedConstructibleLowerShriek ℓ j').obj M))
    (ζ : (centre X I).left) :
    ∃ U : (centre X I).left.Opens, ζ ∈ U ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).obj
        (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (((deformationModel X I k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
              (overRestrictι X I.support.compl)).obj N).obj))) := by
  have hM : IsZero M := IsZero.of_full_of_faithful_of_isZero (boundedConstructible _).ι M
    (isZero_derivedCategory_of_isEmpty ℓ M.obj)
  have hN : IsZero N := ((boundedConstructibleLowerShriek ℓ g).map_isZero
    ((boundedConstructibleLowerShriek ℓ j').map_isZero hM)).of_iso e
  refine ⟨⊤, trivial, Functor.map_isZero _ (Functor.map_isZero _
    (NearbyCyclesModel.isZero_nearbyCycles_obj _ _ ?_))⟩
  exact (boundedConstructible _).ι.map_isZero
    ((boundedConstructibleOpenImmersionLowerShriek _ ℓ _).map_isZero hN)

set_option linter.unusedVariables false in
-- The lisse generator data are part of the interface of the reduction.
/-- **The codimension-one core** (route (a), after the geometric reduction
`isEmpty_or_exists_opens_subset_range`): the hypotheses of
`exists_isZero_upperStar_nearbyCycles_lowerShriek_lisseGenerator_of_mem_closure`, with the
closure condition replaced by its consequence that, on an open neighbourhood `V` of `ζ`, the
lisse generator `Rg_! Rj'_! M` is lisse on all of `V ∖ Z`.

This is the genuine local acyclicity statement: near `ζ` the complex `j_! N` is the extension by
zero of a lisse complex on the complement of the divisor (up to the universal homeomorphism
`U₀ ∩ V ⟶ V ∖ Z`), and `Le^* Ψ_X(j_! N)` vanishes near `ζ`. It holds for every bounded
constructible `N` (`exists_isZero_upperStar_nearbyCycles_lowerShriek_padicAlgCl`), by reduction to
`𝔽_E`-coefficients through an integral model of `N` and derived Nakayama. -/
theorem exists_isZero_upperStar_nearbyCycles_lowerShriek_of_subset_range
    [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    {Z₀ : Over (Spec (.of k))} [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [IsSeparated Z₀.hom] (g : Z₀ ⟶ overRestrict X I.support.compl) [IsClosedImmersion g.left]
    {U₀ : Over (Spec (.of k))} [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom] [IsAffine U₀.left] (j' : U₀ ⟶ Z₀) [IsOpenImmersion j'.left]
    (M : Dᵇc(U₀.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (hM : IsDualizable M)
    (N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (e : N ≅ (boundedConstructibleLowerShriek ℓ g).obj
      ((boundedConstructibleLowerShriek ℓ j').obj M))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (V : X.left.Opens) (hζV : I.subschemeι ζ ∈ V)
    (hV : (V : Set X.left) ∩ (I.support.compl : Set X.left) ⊆
      Set.range (j' ≫ g ≫ overRestrictι X I.support.compl).left.base) :
    ∃ U : (centre X I).left.Opens, ζ ∈ U ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).obj
        (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (((deformationModel X I k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
              (overRestrictι X I.support.compl)).obj N).obj))) :=
  exists_isZero_upperStar_nearbyCycles_lowerShriek_padicAlgCl k' hX hh hI ζ hζ N

/-- **The target modulo the codimension-one core**: route (a) reduces
`exists_isZero_upperStar_nearbyCycles_lowerShriek_lisseGenerator_of_mem_closure` to
`exists_isZero_upperStar_nearbyCycles_lowerShriek_of_subset_range`, by the geometric reduction
`isEmpty_or_exists_opens_subset_range` and the empty case
`exists_isZero_upperStar_nearbyCycles_lowerShriek_of_isEmpty`. -/
theorem exists_isZero_upperStar_nearbyCycles_lowerShriek_lisseGenerator_of_mem_closure
    [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    {Z₀ : Over (Spec (.of k))} [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [IsSeparated Z₀.hom] (g : Z₀ ⟶ overRestrict X I.support.compl) [IsClosedImmersion g.left]
    {U₀ : Over (Spec (.of k))} [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom] [IsAffine U₀.left] (j' : U₀ ⟶ Z₀) [IsOpenImmersion j'.left]
    (M : Dᵇc(U₀.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (hM : IsDualizable M)
    (N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (e : N ≅ (boundedConstructibleLowerShriek ℓ g).obj
      ((boundedConstructibleLowerShriek ℓ j').obj M))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (hζZ₀ : I.subschemeι ζ ∈ closure (Set.range (g ≫ overRestrictι X I.support.compl).left.base)) :
    ∃ U : (centre X I).left.Opens, ζ ∈ U ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).obj
        (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (((deformationModel X I k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
              (overRestrictι X I.support.compl)).obj N).obj))) := by
  rcases isEmpty_or_exists_opens_subset_range hX hh hI g j' ζ hζ hζZ₀ with hU | ⟨V, hζV, hV⟩
  · exact exists_isZero_upperStar_nearbyCycles_lowerShriek_of_isEmpty k' g j' M N e ζ
  · exact exists_isZero_upperStar_nearbyCycles_lowerShriek_of_subset_range k' hX hh hI g j' M hM
      N e ζ hζ V hζV hV

/-- **The local computation at a generic point of a principal divisor for lisse generators**
(the local nearby-cycles computation of the proof of blueprint
`lemma-vanishing-generic-points-principal-divisor--1`, for extensions by zero of lisse generators):
let `X` be normal, `Z = V(h)` for a nonzero global function `h`, `j : X ∖ Z ⟶ X` the complement, `N`
a lisse generator of `Dᵇc(X ∖ Z)⟦ℚ̲̄_ℓ⟧` and `ζ` a generic point of an irreducible component of `Z`.
Then the restriction `Le^* Ψ_X(j_! N)` to the zero section vanishes over a neighbourhood of `ζ`: the
extension by zero is locally acyclic along the divisor near `ζ`. Unfinished. -/
theorem exists_isZero_upperStar_nearbyCycles_lowerShriek_lisseGenerator [IsSepClosed k']
    [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] (hX : IsNormalScheme X.left)
    {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hN : lisseGenerator ℓ (overRestrict X I.support.compl) N)
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left) :
    ∃ U : (centre X I).left.Opens, ζ ∈ U ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).obj
        (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (((deformationModel X I k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
              (overRestrictι X I.support.compl)).obj N).obj))) := by
  obtain ⟨Z₀, _, _, _, g, _, U₀, _, _, _, _, j', _, M, hM, hNM⟩ := hN
  by_cases hζZ₀ : I.subschemeι ζ ∈
      closure (Set.range (g ≫ overRestrictι X I.support.compl).left.base)
  · exact exists_isZero_upperStar_nearbyCycles_lowerShriek_lisseGenerator_of_mem_closure k' hX
      hh hI g j' M hM N hNM.some ζ hζ hζZ₀
  · exact exists_isZero_upperStar_nearbyCycles_lowerShriek_of_notMem_closure k' g _ N hNM.some ζ
      hζZ₀

/-- **Reduction of the local computation to the lisse generators**: for `L` with `Li^* L = 0`,
the restricted specialization `Le^* Ψ_X(L)` vanishes near `ζ` as soon as it does for the
extensions by zero `j_! N` of the lisse generators `N` of `Dᵇc(X ∖ Z)⟦ℚ̲̄_ℓ⟧`. Indeed the
open–closed triangle `j_! Lj^* L ⟶ L ⟶ Ri_* Li^* L ⟶` shows `L ≅ j_! Lj^* L`. -/
theorem exists_isZero_upperStar_nearbyCycles_of_lowerShriek {I : X.left.IdealSheafData}
    (ζ : (centre X I).left)
    (h : ∀ N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      lisseGenerator ℓ (overRestrict X I.support.compl) N →
      nearbyCyclesVanishNear X I k' (Profinite.padicAlgClRingObj ℓ) ζ
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (overRestrictι X I.support.compl)).obj N).obj)
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hL : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (centreι X I)).obj L)) :
    nearbyCyclesVanishNear X I k' (Profinite.padicAlgClRingObj ℓ) ζ L.obj := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_openImmersionLowerShriek_openClosed
    (overRestrictι X I.support.compl) (centreι X I) (isCompl_range_overRestrictι_centreι I) L
  have h₃ : IsZero ((boundedConstructible _).ι.obj ((boundedConstructibleLowerStar ℓ
      (centreι X I)).obj ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (centreι X I)).obj L))) :=
    (boundedConstructible _).ι.map_isZero ((boundedConstructibleLowerStar ℓ _).map_isZero hL)
  have : IsIso ((boundedConstructible _).ι.map
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
        (overRestrictι X I.support.compl)).counit.app L)) :=
    (Triangle.isZero₃_iff_isIso₁ _ hδ).1 h₃
  exact (nearbyCyclesVanishNear X I k' _ ζ).prop_of_iso (asIso ((boundedConstructible _).ι.map
    ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
      (overRestrictι X I.support.compl)).counit.app L)))
    (nearbyCyclesVanishNear_lowerShriek_of_lisseGenerator k' ζ h _)

end AlgebraicGeometry.ProEtale.CondensedRing
