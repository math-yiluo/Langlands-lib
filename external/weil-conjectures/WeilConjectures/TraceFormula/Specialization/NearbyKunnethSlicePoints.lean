/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.Coordinates
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethFiniteSupport
public import WeilConjectures.Tactic.ExactModProofs

/-!

# The non-closed points of the special fibre of a product are reached by generic slices

Let `P` be the product over the strictly henselian trait `S = Spec k'⟦t⟧` of models `M`, `N` of
finite type whose total spaces locally embed into `𝔸ᵐ_S`, `𝔸^{m'}_S`. If the generic-slicing
step of Gabber's Künneth formula holds in chart dimension `m + m' - 1` with coefficients `Λ`
(`NearbyCyclesModel.SliceKunnethFormula`), then every point `z` of the special fibre `X_s × Y_s`
which is not closed lies in the image of a morphism `h : W ⟶ X_s × Y_s` along which the pullback
of the Künneth map `Π_{A,B}` is invertible
(`NearbyCyclesModel.exists_isIso_map_kunnethMap_of_not_isClosed`): around `z`, the coordinates of
charts of the total spaces detect closed points, so one of them sends `z` to the generic point of
the special-fibre line, and `z` comes from the special fibre of the generic slice along it
(`NearbyCyclesModel.mem_range_sliceSpecialMap`).

This is the input of the closed-point criterion
(`ProEtale.CondensedRing.isIso_of_isIso_leftDerivedUpperStar_map_of_not_isClosed`) in the proof of
Gabber's formula with torsion coefficients, as the finite-support step
(`NearbyCyclesModel.exists_finite_isIso_upperStar_map_kunnethMap_of_boundedConstructible`) is for
`ℚ̄_ℓ`-coefficients.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k' : Type u} [Field k'] {X Y Z : Scheme.{u}}
  {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'}
  {φ₂ : P.Hom N f₂ f₂'} {qM : M.total ⟶ trait k'}
  {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

/-- Slicing an immersion along one coordinate gives a chart with that coordinate removed. -/
private lemma locallyEmbedsInAffineSpace_pullback_reindex {T S S' : Scheme.{u}}
    {ι : Type u} [Finite ι] (c : T ⟶ 𝔸(ι; S)) [IsImmersion c] (a : ι)
    (σ : S' ⟶ 𝔸(ULift.{u} (Fin 1); S)) :
    (pullback.snd (c ≫ AffineSpace.reindex (fun _ ↦ a) S) σ).LocallyEmbedsInAffineSpace
      (Nat.card {j : ι // j ≠ a}) := by
  obtain ⟨c', hc'i, hc'⟩ := exists_isImmersion_pullback_reindex c a σ
  exact Scheme.Hom.LocallyEmbedsInAffineSpace.of_isImmersion c' hc'

/-- Closed coordinates of a chart, pulled back along a morphism of models, detect a closed
image point on the special fibre. -/
private lemma isClosed_singleton_of_specialCoordinate_comp_hom
    (hM : M.IsTraitModelOver qM gM) (φ : P.Hom M f₁ f₁')
    {qP : P.total ⟶ trait k'} {gP : P.generic ⟶ Spec (.of (traitGenericField k'))}
    (hP : P.IsTraitModelOver qP gP) (hqP : qP = φ.total ≫ qM)
    {ι : Type u} (c : M.total ⟶ 𝔸(ι; trait k')) [IsImmersion c]
    (hc : c ≫ 𝔸(ι; trait k') ↘ trait k' = qM) (z : Z'.left)
    (hcoord : ∀ a : ι, (φ.total ≫ c ≫ AffineSpace.reindex
      (fun _ : ULift.{u} (Fin 1) ↦ a) (trait k')) ≫
        𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qP)
    (hz : ∀ a, IsClosed {(specialCoordinate hP
      (φ.total ≫ c ≫ AffineSpace.reindex (fun _ ↦ a) (trait k')) (hcoord a) z)}) :
    IsClosed {f₁' z} := by
  refine isClosed_singleton_of_isImmersion hM c hc _ fun a ↦ ?_
  have h := hz a
  rwa [show specialCoordinate hP
      (φ.total ≫ c ≫ AffineSpace.reindex (fun _ ↦ a) (trait k')) (hcoord a) =
      f₁' ≫ specialCoordinate hM c hc ≫
        AffineSpace.reindex (fun _ ↦ a) (Spec (.of k')) by
    rw [← specialCoordinate_comp_reindex hM c hc]
    exact specialCoordinate_comp_hom hM φ hP hqP _ _, Scheme.Hom.comp_apply] at h

/-- On global affine charts, a non-closed point is reached by a slice on which the Künneth
map is invertible. -/
private theorem exists_isIso_map_kunnethMap_of_not_isClosed_of_charts
    [TopologicalSpace.NoetherianSpace X] [TopologicalSpace.NoetherianSpace Y]
    [TopologicalSpace.NoetherianSpace Z]
    (hM : M.IsTraitModelOver qM gM) (hN : N.IsTraitModelOver qN gN)
    (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) {m m' : ℕ}
    (hm : qM.LocallyEmbedsInAffineSpace m) (hm' : qN.LocallyEmbedsInAffineSpace m')
    (hslice : 0 < m + m' → SliceKunnethFormula Λ k' (m + m' - 1))
    {ι κ : Type u} [Finite ι] [Finite κ]
    (cM : M.total ⟶ 𝔸(ι; trait k')) [IsImmersion cM]
    (hcM : cM ≫ 𝔸(ι; trait k') ↘ trait k' = qM) (hcardM : Nat.card ι ≤ m)
    (cN : N.total ⟶ 𝔸(κ; trait k')) [IsImmersion cN]
    (hcN : cN ≫ 𝔸(κ; trait k') ↘ trait k' = qN) (hcardN : Nat.card κ ≤ m')
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (hA : boundedConstructible (condensedRingObj Λ X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))} (hB : boundedConstructible (condensedRingObj Λ Y) B)
    (z : Z'.left) (hz : ¬ IsClosed ({z} : Set Z'.left)) :
    ∃ (W : Scheme.{u}) (h : W ⟶ Z'.left) (w : W), h w = z ∧
      IsIso (L((h)^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B)) := by
  let coord : ι ⊕ κ → (P.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')) :=
    Sum.elim (fun a ↦ φ₁.total ≫ cM ≫ AffineSpace.reindex (fun _ ↦ a) (trait k'))
      (fun a ↦ φ₂.total ≫ cN ≫ AffineSpace.reindex (fun _ ↦ a) (trait k'))
  have hcoord : ∀ i, coord i ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' =
      φ₁.total ≫ qM := by
    rintro (a | a)
    · simp [coord, hcM]
    · simp [coord, hcN, hpb.w]
  obtain ⟨i, hi⟩ : ∃ i, ¬ IsClosed {specialCoordinate hP (coord i) (hcoord i) z} := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hz
    exact isClosed_singleton_special hM hN hpb hP z
      (isClosed_singleton_of_specialCoordinate_comp_hom hM φ₁ hP rfl cM hcM z
        (fun a ↦ hcoord (.inl a)) (fun a ↦ hall (.inl a)))
      (isClosed_singleton_of_specialCoordinate_comp_hom hN φ₂ hP hpb.w cN hcN z
        (fun a ↦ hcoord (.inr a)) (fun a ↦ hall (.inr a)))
  obtain ⟨w, hw⟩ := mem_range_sliceSpecialMap (traitSliceCoord k')
    (transcendental_traitSliceCoord k') hP (hcoord i) z
    (AffineSpace.isGenericPoint_of_not_isClosed hi)
  refine ⟨_, sliceSpecialMap (traitSliceCoord k') hP (hcoord i), w, hw, ?_⟩
  rcases i with a | a
  · have hlt : Nat.card {j : ι // j ≠ a} < Nat.card ι :=
      Finite.card_subtype_lt (x := a) (by simp)
    exact (hslice (by omega)).isIso φ₁ φ₂ hM hN hpb hP hgen inferInstance inferInstance
      inferInstance (b := cM ≫ AffineSpace.reindex (fun _ ↦ a) (trait k')) (by simp [hcM])
      (by omega) (locallyEmbedsInAffineSpace_pullback_reindex cM a _)
      hm' heM heN hA hB
  · have hlt : Nat.card {j : κ // j ≠ a} < Nat.card κ :=
      Finite.card_subtype_lt (x := a) (by simp)
    exact isIso_map_kunnethMap_baseChangeSpecialMap_snd hM hN hpb hP hgen
      (b := cN ≫ AffineSpace.reindex (fun _ ↦ a) (trait k')) (by simp [hcN]) _
      (hslice (by omega)) (by omega) hm
      (locallyEmbedsInAffineSpace_pullback_reindex cN a _) heM heN hA hB

/-- **The non-closed points are reached by generic slices**: under the generic-slicing step in
chart dimension `m + m' - 1` with coefficients `Λ`, every point `z` of the special fibre of the
product which is not closed is the image of a point under a morphism `h : W ⟶ X_s × Y_s` along
which the pullback of the Künneth map `Π_{A,B}` is invertible. -/
theorem exists_isIso_map_kunnethMap_of_not_isClosed [TopologicalSpace.NoetherianSpace X]
    [TopologicalSpace.NoetherianSpace Y] [TopologicalSpace.NoetherianSpace Z]
    (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) {m m' : ℕ}
    (hm : qM.LocallyEmbedsInAffineSpace m) (hm' : qN.LocallyEmbedsInAffineSpace m')
    (hslice : 0 < m + m' → SliceKunnethFormula Λ k' (m + m' - 1))
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (hA : boundedConstructible (condensedRingObj Λ X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))}
    (hB : boundedConstructible (condensedRingObj Λ Y) B) (z : Z'.left)
    (hz : ¬ IsClosed ({z} : Set Z'.left)) :
    ∃ (W : Scheme.{u}) (h : W ⟶ Z'.left) (w : W), h w = z ∧
      IsIso (L((h)^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B)) := by
  have : LocallyOfFiniteType Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i
    hP.locallyOfFiniteType
  have : JacobsonSpace Z'.left := LocallyOfFiniteType.jacobsonSpace Z'.hom
  have := hM.isTraitModel.isNoetherian_total
  have := hN.isTraitModel.isNoetherian_total
  have := hP.isTraitModel.isNoetherian_total
  -- Choose charts before applying the argument for abstract, globally charted models.
  obtain ⟨V, hzV, ιV, _, cV, hcardV, hcVi, hcV⟩ := hm (φ₁.total (P.i z))
  obtain ⟨W, hzW, ιW, _, cW, hcardW, hcWi, hcW⟩ := hm' (φ₂.total (P.i z))
  have : QuasiCompact V.ι := inferInstance
  have : QuasiCompact W.ι := inferInstance
  have : QuasiCompact (productOpen φ₁ φ₂ V W).ι := inferInstance
  let U := productOpen φ₁ φ₂ V W
  let ψ₁ := φ₁.restrictOpen U V inf_le_left
  let ψ₂ := φ₂.restrictOpen U W inf_le_right
  have hMV := hM.restrictOpen V
  have hNW := hN.restrictOpen W
  have hpbU : IsPullback ψ₁.total ψ₂.total (V.ι ≫ qM) (W.ι ≫ qN) := isPullback_resLE_inf hpb V W
  have hPU := isTraitModelOver_restrictOpen_productOpen (φ₂ := φ₂) hP V W
  have heMV : (M.restrictOpen V).j ≫ V.ι ≫ eM = (M.restrictOpen V).ε := by simp [← heM]
  have heNW : (N.restrictOpen W).j ≫ W.ι ≫ eN = (N.restrictOpen W).ε := by simp [← heN]
  have hgenU : ψ₂.generic ≫ (N.j ⁻¹ᵁ W).ι ≫ gN = ψ₁.generic ≫ (M.j ⁻¹ᵁ V).ι ≫ gM := by
    simp [ψ₁, ψ₂, Scheme.Hom.resLE_comp_ι_assoc, hgen]
  let v : P.i ⁻¹ᵁ U := ⟨z, hzV, hzW⟩
  have hv : ¬ IsClosed ({v} : Set (P.i ⁻¹ᵁ U)) := fun h ↦
    hz ((P.i ⁻¹ᵁ U).ι.closedPoints_subset_preimage_closedPoints h)
  have hA' := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ (𝟙 X) _ hA
  have hB' := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ (𝟙 Y) _ hB
  obtain ⟨T, t, w, hw, ht⟩ := exists_isIso_map_kunnethMap_of_not_isClosed_of_charts Λ
    hMV hNW hpbU hPU hgenU (hm.restrict V) (hm'.restrict W) hslice
    cV hcV hcardV cW hcW hcardW heMV heNW hA' hB' v hv
  let r' : (P.restrictSpecialFibre U).left ⟶ Z'.left := (P.i ⁻¹ᵁ U).ι
  refine ⟨T, t ≫ r', w, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply, hw]
    rfl
  have hR := isKunnethRestriction_restrictOpen φ₁ φ₂ V W
  have ht' : IsIso (L((t)^*⟦Λ⟧).map (L((r')^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B))) := by
    exact (isIso_map_map_kunnethMap_iff_of_isKunnethRestriction Λ hR _ A B).2 ht
  exact (NatIso.isIso_map_iff (leftDerivedUpperStarComp Λ t r') _).2 ht'

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
