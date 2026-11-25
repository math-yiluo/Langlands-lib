/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersion

/-!

# Reduction modulo `ℓⁿ` commutes with the pushforward along a closed immersion

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and
`k` a field of characteristic `p ≠ ℓ`. For a separated `k`-scheme of finite type `X` write
`red_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦𝒪_E ⧸ ℓⁿ⟧` for the reduction modulo `ℓⁿ`
(`ProEtale.boundedConstructibleIntegersModPowReduction`). For a morphism `d : Z ⟶ Y` this file
defines the comparison
```
γ : Rd_*^{𝒪_E} ⋙ red_Y ⟶ red_Z ⋙ Rd_*^{𝒪_E ⧸ ℓⁿ}
```
(`ProEtale.CondensedRing.boundedConstructibleLowerStarIntegersModPowReduction`), the mate of the
inverse of the pullback comparison
(`ProEtale.CondensedRing.boundedConstructibleUpperStarIntegersModPowReductionIso`) under the
adjunctions `d^* ⊣ Rd_*`, and proves that it is an isomorphism when `d` is a closed immersion
(`ProEtale.CondensedRing.isIso_boundedConstructibleLowerStarIntegersModPowReduction`).

The proof checks the isomorphism after the jointly conservative pair of restrictions `d^*` and
`j^*`, where `j : U ⟶ Y` is the open complement of `d` (`AlgebraicGeometry.overOpenComplement`):

* after `d^*`, composing with the counit `d^* Rd_* ⟶ 𝟭` (an isomorphism, as `Rd_*` is fully
  faithful) gives the pullback comparison followed by the reduction of the counit;
* after `j^*`, both sides vanish, since `j^* Rd_* = 0` and the reduction commutes with `j^*` and
  preserves zero objects.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

/-! ### The open complement of a closed immersion -/

section OpenComplement

variable {S : Scheme.{u}} {Z Y : Over S} (d : Z ⟶ Y) [IsClosedImmersion d.left]

/-- The open complement of the range of a closed immersion `d : Z ⟶ Y` of `S`-schemes, an open
subset of `Y`. -/
noncomputable def overOpenComplementOpens : Y.left.Opens :=
  ⟨(Set.range d.left.base)ᶜ, d.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The open complement of a closed immersion `d : Z ⟶ Y` of `S`-schemes, as an object of
`Over S`. -/
noncomputable abbrev overOpenComplementObj : Over S :=
  Over.mk ((overOpenComplementOpens d).ι ≫ Y.hom)

/-- The open immersion of the open complement of a closed immersion `d : Z ⟶ Y` of `S`-schemes,
as a morphism of `Over S`. -/
noncomputable abbrev overOpenComplement : overOpenComplementObj d ⟶ Y :=
  Over.homMk (overOpenComplementOpens d).ι

/-- The open complement of a closed immersion is an open immersion. -/
instance : IsOpenImmersion (overOpenComplement d).left :=
  inferInstanceAs (IsOpenImmersion (overOpenComplementOpens d).ι)

/-- The open complement of a closed immersion into an `S`-scheme locally of finite type is
locally of finite type. -/
instance [LocallyOfFiniteType Y.hom] : LocallyOfFiniteType (overOpenComplementObj d).hom :=
  inferInstanceAs (LocallyOfFiniteType ((overOpenComplementOpens d).ι ≫ Y.hom))

/-- The open complement of a closed immersion into a separated `S`-scheme is separated. -/
instance [IsSeparated Y.hom] : IsSeparated (overOpenComplementObj d).hom :=
  inferInstanceAs (IsSeparated ((overOpenComplementOpens d).ι ≫ Y.hom))

/-- The open complement of `d` is supported on the complement of the range of `d`. -/
lemma range_overOpenComplement :
    Set.range (overOpenComplement d).left.base = (Set.range d.left.base)ᶜ :=
  Scheme.Opens.range_ι _

/-- The ranges of a closed immersion and of its open complement are complementary. -/
lemma isCompl_range_overOpenComplement :
    IsCompl (Set.range d.left.base) (Set.range (overOpenComplement d).left.base) := by
  rw [range_overOpenComplement]
  exact isCompl_compl

end OpenComplement

section OverField

variable {k : Type u} [Field k] {Z Y : Over (Spec (.of k))} (d : Z ⟶ Y) [IsClosedImmersion d.left]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]

/-- The open immersion of the open complement of a closed immersion into a quasi-compact scheme
locally of finite type over a field is quasi-compact, the target being noetherian. -/
instance : QuasiCompact (overOpenComplement d).left := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Y.left := ⟨⟩
  exact inferInstanceAs (QuasiCompact (overOpenComplementOpens d).ι)

/-- The open complement of a closed immersion into a quasi-compact scheme locally of finite type
over a field is quasi-compact. -/
instance : QuasiCompact (overOpenComplementObj d).hom :=
  inferInstanceAs (QuasiCompact ((overOpenComplement d).left ≫ Y.hom))

end OverField

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section ClosedImmersion

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- For a closed immersion `i`, every restriction `F : Dᵇc(Z)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` of the derived
pushforward `Ri_*` is fully faithful: the counit of an adjunction `G ⊣ F` is an isomorphism. -/
lemma isIso_counit_of_isClosedImmersion_of_lowerStarCompatibility {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {G : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Z)⟦Λ⟧} {F : Dᵇc(Z)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧} (adj : G ⊣ F)
    (e : F ⋙ (boundedConstructible _).ι ≅ (boundedConstructible _).ι ⋙ R((i)_*⟦Λ⟧)) :
    IsIso adj.counit := by
  have h : (F ⋙ (boundedConstructible _).ι).FullyFaithful :=
    ((ObjectProperty.fullyFaithfulι _).comp (Functor.FullyFaithful.ofFullyFaithful _)).ofIso
      e.symm
  have h' := h.ofCompFaithful
  have := h'.full
  have := h'.faithful
  exact adj.counit_isIso_of_R_fully_faithful

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **`Lj^* Ri_*` vanishes on bounded constructible complexes** when the ranges of the open
immersion `j` and of `i` are disjoint, for every right adjoint `F` of `Li^*` on bounded
constructible complexes: by the adjunctions `j_! ⊣ Lj^*` and `Li^* ⊣ F`, a morphism
`M ⟶ Lj^* F N` is a morphism `Li^* j_! M ⟶ N`, and `Li^* j_! = 0`
(`ProEtale.CondensedRing.isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek`). -/
lemma isZero_boundedConstructibleUpperStar_obj_of_upperStarAdjunction
    {Z U X : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] (i : Z ⟶ X) {F : Dᵇc(Z.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧}
    (adj : boundedConstructibleUpperStar Λ ℓ i ⊣ F)
    (hji : Disjoint (Set.range j.left.base) (Set.range i.left.base)) (N : Dᵇc(Z.left)⟦Λ⟧) :
    IsZero ((boundedConstructibleUpperStar Λ ℓ j).obj (F.obj N)) := by
  rw [IsZero.iff_id_eq_zero]
  refine ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).homEquiv _
    _).symm.injective ((adj.homEquiv _ _).symm.injective ?_)
  exact (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek Λ ℓ j i hji _).eq_of_src
    _ _

end ClosedImmersion

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-- The reduction modulo `ℓⁿ` on bounded constructible complexes preserves zero objects, as the
derived extension of scalars, a left adjoint, does. -/
lemma isZero_boundedConstructibleIntegersModPowReduction_obj (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    {M : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E⟧} (hM : IsZero M) :
    IsZero ((boundedConstructibleIntegersModPowReduction X ℓ E n).obj M) := by
  have := (Mod.derivedExtendMapDerivedCategoryAdjunction
    (integersModPowReduction X ℓ E n)).isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint
    (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor
  have h : IsZero ((boundedConstructible _).ι.obj
      ((boundedConstructibleIntegersModPowReduction X ℓ E n).obj M)) :=
    (Functor.map_isZero _ (Functor.map_isZero _ hM)).of_iso
      ((boundedConstructibleIntegersModPowReductionCompatibility X ℓ E n).app M)
  rw [IsZero.iff_id_eq_zero] at h ⊢
  exact (boundedConstructible _).ι.map_injective (by simpa using h)

variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [TopologicalSpace.NoetherianSpace Z.left]
  [TopologicalSpace.NoetherianSpace Y.left] (d : Z ⟶ Y)

/-- **Reduction modulo `ℓⁿ` and the pushforward** on bounded constructible complexes: the
comparison `γ : Rd_*^{𝒪_E} ⋙ red_Y ⟶ red_Z ⋙ Rd_*^{𝒪_E ⧸ ℓⁿ}`, the mate of the inverse of the
pullback comparison `boundedConstructibleUpperStarIntegersModPowReductionIso` under the
adjunctions `d^* ⊣ Rd_*`. -/
noncomputable def boundedConstructibleLowerStarIntegersModPowReduction :
    PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E d ⋙
        boundedConstructibleIntegersModPowReduction Y.left ℓ E n ⟶
      boundedConstructibleIntegersModPowReduction Z.left ℓ E n ⋙
        IntegersModPowRingObj.boundedConstructibleLowerStar ℓ E n d :=
  mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E d)
    (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n d)
    (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n d).inv

/-- **Reduction modulo `ℓⁿ` commutes with the pushforward along a closed immersion**: the
comparison `γ : Rd_*^{𝒪_E} ⋙ red_Y ⟶ red_Z ⋙ Rd_*^{𝒪_E ⧸ ℓⁿ}` is an isomorphism. It is checked
after the restrictions `d^*` and `j^*` to `Z` and to its open complement `j : U ⟶ Y`: after `d^*`
and the counit isomorphism `d^* Rd_* ≅ 𝟭`, `γ` becomes the pullback comparison followed by the
reduction of the counit, and after `j^*` both sides vanish. -/
theorem isIso_boundedConstructibleLowerStarIntegersModPowReduction [IsClosedImmersion d.left] :
    IsIso (boundedConstructibleLowerStarIntegersModPowReduction ℓ E n d) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  refine isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl _ ℓ d (overOpenComplement d)
    (isCompl_range_overOpenComplement d) _ ?_ ?_
  · have : TopologicalSpace.NoetherianSpace (overOpenComplementObj d).left :=
      TopologicalSpace.NoetherianSpace.set (α := Y.left) _
    have hd := (isCompl_range_overOpenComplement d).disjoint.symm
    have hsrc := (isZero_boundedConstructibleIntegersModPowReduction_obj ℓ E n _
      (isZero_boundedConstructibleUpperStar_obj_of_upperStarAdjunction _ ℓ (overOpenComplement d)
        d (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E d) hd
        K)).of_iso ((boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n
          (overOpenComplement d)).app _).symm
    have htgt := isZero_boundedConstructibleUpperStar_obj_of_upperStarAdjunction _ ℓ
      (overOpenComplement d) d
      (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n d) hd
      ((boundedConstructibleIntegersModPowReduction Z.left ℓ E n).obj K)
    exact ⟨0, hsrc.eq_of_src _ _, htgt.eq_of_src _ _⟩
  · have := isIso_counit_of_isClosedImmersion_of_lowerStarCompatibility _ d.left
      (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E d)
      (PadicIntegersRingObj.boundedConstructibleLowerStarCompatibility ℓ E d)
    have := isIso_counit_of_isClosedImmersion_of_lowerStarCompatibility _ d.left
      (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n d)
      (IntegersModPowRingObj.boundedConstructibleLowerStarCompatibility ℓ E n d)
    exact IsIso.of_isIso_fac_right (mateEquiv_counit
      (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E d)
      (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n d)
      (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n d).inv K)

/-- Reduction modulo `ℓⁿ` commutes with the pushforward along a closed immersion:
`Rd_*^{𝒪_E} ⋙ red_Y ≅ red_Z ⋙ Rd_*^{𝒪_E ⧸ ℓⁿ}`. -/
noncomputable def boundedConstructibleLowerStarIntegersModPowReductionIso
    [IsClosedImmersion d.left] :
    PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E d ⋙
        boundedConstructibleIntegersModPowReduction Y.left ℓ E n ≅
      boundedConstructibleIntegersModPowReduction Z.left ℓ E n ⋙
        IntegersModPowRingObj.boundedConstructibleLowerStar ℓ E n d :=
  haveI := isIso_boundedConstructibleLowerStarIntegersModPowReduction ℓ E n d
  asIso (boundedConstructibleLowerStarIntegersModPowReduction ℓ E n d)

end AlgebraicGeometry.ProEtale.CondensedRing
