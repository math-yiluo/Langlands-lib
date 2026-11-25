/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Closed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale

/-!

# Exceptional inverse images of closed immersions and weakly étale base change

Let `k₁` and `k₂` be fields and `i : Z ⟶ P` a closed immersion of separated `k₁`-schemes of finite
type with a cartesian square
```
Z' --πZ--> Z
 |i'       |i
 v         v
P' --πP--> P
```
where `i' : Z' ⟶ P'` is a closed immersion of separated `k₂`-schemes of finite type. If `πP` is
weakly étale, the base change map `γ : πZ^* Ri^! ⟶ Ri'^! πP^*` of the exceptional inverse image
(`ProEtale.CondensedRing.upperShriekBaseChangeOfMap`) is an isomorphism on bounded constructible
`ℚ̄_ℓ`-complexes (`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_weaklyEtale`).
This applies for instance to the inclusion of the generic point of `𝔸¹_k`, which changes the
base field from `k` to `k(t)`.

## Proof

As in `ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_fieldExtension`: complete
the unit `M ⟶ Rj_* j^* M` (`j : V ⟶ P` the open complement of `i`) to a distinguished triangle;
its pullback along `πP` is distinguished, and its third term `πP^* Rj_* j^* M` is
`Rj'_* πV^* j^* M` by weakly étale base change
(`ProEtale.CondensedRing.isIso_baseChangeMap_of_weaklyEtale`, for the weakly étale restriction
`πV = πP ∣_ V`), which receives no maps from `Ri'_*`. Unlike the case of a field extension, no
finiteness condition on `M` is needed for this base change.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option hygiene false in
/-- The coefficient ring `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {P Z : Over (Spec (.of k₁))} [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
  [IsSeparated P.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {P' Z' : Over (Spec (.of k₂))} [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom]
  [IsSeparated P'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {i : Z ⟶ P} {i' : Z' ⟶ P'} [IsClosedImmersion i.left] [IsClosedImmersion i'.left]
  {πP : P'.left ⟶ P.left} {πZ : Z'.left ⟶ Z.left}

/-- **The base change map of a closed exceptional inverse image along a weakly étale morphism is
an isomorphism**: for a closed immersion `i : Z ⟶ P` of separated `k₁`-schemes of finite type, a
cartesian square `πZ ≫ i = i' ≫ πP` with `i' : Z' ⟶ P'` a closed immersion of separated
`k₂`-schemes of finite type and `πP` weakly étale, and a bounded constructible `ℚ̄_ℓ`-complex `M`
on `P`, the canonical map `πZ^* Ri^! M ⟶ Ri'^! πP^* M` is invertible. -/
theorem isIso_upperShriekBaseChangeOfMap_app_of_weaklyEtale [WeaklyEtale πP]
    (sq : IsPullback πZ i'.left i.left πP) (M : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((upperShriekBaseChangeOfMap ℓ sq).app M) := by
  /- The open complement `V` of `i` and its preimage `V'` in `P'`. -/
  let V : P.left.Opens :=
    ⟨(Set.range i.left.base)ᶜ, i.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hV : Set.range V.ι.base = (Set.range i.left.base)ᶜ := Scheme.Opens.range_ι V
  have hcompl : IsCompl (Set.range i.left.base) (Set.range V.ι.base) := by
    rw [hV]
    exact isCompl_compl
  let V' : P'.left.Opens := πP ⁻¹ᵁ V
  have hV' : Disjoint (Set.range V'.ι.base) (Set.range i'.left.base) := by
    rw [Scheme.Opens.range_ι, Set.disjoint_left]
    rintro _ hx ⟨z, rfl⟩
    have hx' : πP.base (i'.left.base z) ∉ Set.range i.left.base := hx
    refine hx' ⟨πZ.base z, ?_⟩
    rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
  have sqV : IsPullback (πP ∣_ V) V'.ι V.ι πP := isPullback_morphismRestrict πP V
  /- The triangle `X ⟶ M ⟶ Rj_* j^* M ⟶`. -/
  let adjV := derivedUpperStarLowerStarAdjunction 𝐐 V.ι
  obtain ⟨X, f, h, hT⟩ := distinguished_cocone_triangle₁ (adjV.unit.app M.obj)
  have hjX := isZero_map_obj_of_distinguished_unit_triangle adjV f h hT
  have hiX : IsIso ((derivedUpperStarLowerStarAdjunction 𝐐 i.left).unit.app X) :=
    isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero _ V.ι i.left hcompl hjX
  have : LocallyOfFiniteType (Over.mk (V.ι ≫ P.hom)).hom :=
    inferInstanceAs (LocallyOfFiniteType (V.ι ≫ P.hom))
  have : QuasiCompact (Over.mk (V.ι ≫ P.hom)).hom :=
    inferInstanceAs (QuasiCompact (V.ι ≫ P.hom))
  have : IsSeparated (Over.mk (V.ι ≫ P.hom)).hom :=
    inferInstanceAs (IsSeparated (V.ι ≫ P.hom))
  have hjM := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ V.ι M.obj M.property
  have hRj := boundedConstructible_rightDerivedLowerStar_obj ℓ
    (Over.homMk V.ι : Over.mk (V.ι ≫ P.hom) ⟶ P) ⟨_, hjM⟩
  have hX : boundedConstructible _ X :=
    (boundedConstructible _).ext_of_isTriangulatedClosed₁ _ hT M.property hRj
  /- The closed part `Q₀ = Li^* X`, with `Ri_* Q₀ ≅ X`. -/
  let Q₀ : Dᵇc(Z.left)⟦𝐐⟧ :=
    ⟨(L((i.left)^*⟦𝐐⟧)).obj X,
      boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ i.left X hX⟩
  let e₁ : (boundedConstructible _).ι.obj ((boundedConstructibleLowerStar ℓ i).obj Q₀) ≅ X :=
    (asIso ((derivedUpperStarLowerStarAdjunction 𝐐 i.left).unit.app X)).symm
  have hLi : (boundedConstructibleLowerStar ℓ i ⋙ (boundedConstructible _).ι).FullyFaithful :=
    ((ObjectProperty.fullyFaithfulι _).comp
      (derivedUpperStarLowerStarAdjunction 𝐐 i.left).fullyFaithfulROfIsIsoCounit).ofIso
      (boundedConstructibleLowerStarCompatibility ℓ i).symm
  have hLi' : (boundedConstructibleLowerStar ℓ i' ⋙ (boundedConstructible _).ι).FullyFaithful :=
    ((ObjectProperty.fullyFaithfulι _).comp
      (derivedUpperStarLowerStarAdjunction 𝐐 i'.left).fullyFaithfulROfIsIsoCounit).ofIso
      (boundedConstructibleLowerStarCompatibility ℓ i').symm
  /- The pulled back triangle; its third term is computed by weakly étale base change. -/
  let Tr := Triangle.mk f (adjV.unit.app M.obj) h
  have hT' : (L((πP)^*⟦𝐐⟧)).mapTriangle.obj Tr ∈ distTriang _ :=
    (L((πP)^*⟦𝐐⟧)).map_distinguished _ hT
  have : IsIso (baseChangeMap 𝐐 sqV.toCommSq) := isIso_baseChangeMap_of_weaklyEtale 𝐐 sqV
  let e₃ := asIso ((baseChangeMap 𝐐 sqV.toCommSq).app ((L((V.ι)^*⟦𝐐⟧)).obj M.obj))
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sq
  exact isIso_mateEquiv_inv_app_of_triangle (lowerStarUpperShriekAdjunction ℓ i)
    (lowerStarUpperShriekAdjunction ℓ i') (boundedConstructibleBaseChangeOfMap ℓ sq.toCommSq)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _) hLi hLi'
    (L((πP)^*⟦𝐐⟧)) (ObjectProperty.liftCompιIso _ _ _) Tr hT hT' e₁ (Iso.refl _)
    (fun Q ↦ adjV.subsingleton_hom_of_isZero
      (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint _ V.ι i.left
        hcompl.symm.disjoint Q.obj) _)
    (fun Q ↦ subsingleton_hom_rightDerivedLowerStar_shift_of_disjoint _ V.ι i.left
        hcompl.symm.disjoint Q.obj _ _)
    (fun Q ↦ @Equiv.subsingleton _ _ (Iso.homCongr (Iso.refl _) e₃)
      ((derivedUpperStarLowerStarAdjunction 𝐐 V'.ι).subsingleton_hom_of_isZero
        (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint _ V'.ι i'.left
          hV' Q.obj) _))
    (fun Q ↦ @Equiv.subsingleton _ _
      (Iso.homCongr (Iso.refl _) ((shiftFunctor _ (-1 : ℤ)).mapIso e₃))
      (subsingleton_hom_rightDerivedLowerStar_shift_of_disjoint _ V'.ι i'.left hV' Q.obj _ _))

/-- **The base change map of a closed exceptional inverse image along a weakly étale morphism is
an isomorphism**, as an isomorphism of functors `πZ^* Ri^! ≅ Ri'^! πP^*`. -/
instance isIso_upperShriekBaseChangeOfMap_of_weaklyEtale [WeaklyEtale πP]
    (sq : IsPullback πZ i'.left i.left πP) : IsIso (upperShriekBaseChangeOfMap ℓ sq) :=
  have := isIso_upperShriekBaseChangeOfMap_app_of_weaklyEtale ℓ sq
  NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.ProEtale.CondensedRing
