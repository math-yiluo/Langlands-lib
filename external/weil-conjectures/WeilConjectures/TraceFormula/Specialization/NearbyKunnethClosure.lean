/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethGeneric
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing
public import WeilConjectures.TraceFormula.Specialization.TraitModelEmbedding
public import WeilConjectures.TraceFormula.Specialization.TraitProductRestrict

/-!

# Gabber's Künneth formula for nearby cycles: passing to proper closures

Let `P` be the product over the trait `S = Spec k'⟦t⟧` of models `M`, `N` of finite type over `S`
along `qM : 𝒳 ⟶ S`, `qN : 𝒴 ⟶ S`, whose identifications factor through the total spaces,
`ε_M = j ≫ e_M`, `ε_N = j ≫ e_N`, and whose second projection is compatible with the structure
morphisms of the geometric generic fibres to `Spec Ω`. Given open immersions `𝒳 ⟶ 𝒳̄`,
`𝒴 ⟶ 𝒴̄` over `S` into proper `S`-schemes, this file shows that Gabber's Künneth formula for the
product `𝒳̄ ×_S 𝒴̄` of the standard models of `𝒳̄`, `𝒴̄` implies it for `P`
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.isIso_kunnethMap_of_closure`):

* the Künneth map is natural in the coefficients
  (`NearbyCyclesModel.kunnethMap_naturality`);
* the Künneth map of `P` is the Künneth map of the models of the total spaces, applied to
  `Le_M^* A`, `Le_N^* B` (`NearbyCyclesModel.isIso_kunnethMap_of_toGeometricGeneric`); these
  models are restrictions of the standard models of `𝒳̄`, `𝒴̄`, `𝒳̄ ×_S 𝒴̄` along open immersions
  with cartesian squares of geometric generic fibres;
* by the restriction of the Künneth map to opens
  (`NearbyCyclesModel.isIso_map_kunnethMap_iff_of_isKunnethRestriction`) applied to the
  extensions by zero `u_! A`, `u_! B` (with `Lu^* u_! ≅ 𝟭`), the Künneth map of the models of the
  total spaces is invertible if the one of the closures is.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Abstract

variable {CM CN CP SM SN T : Type*} [Category CM] [Category CN] [Category CP] [Category SM]
  [Category SN] [Category T] [MonoidalCategory CP] [MonoidalCategory T]
  {ΨM : CM ⥤ SM} {ΨN : CN ⥤ SN} {ΨP : CP ⥤ T} {s₁ : SM ⥤ T} {s₂ : SN ⥤ T} {g₁ : CM ⥤ CP}
  {g₂ : CN ⥤ CP}

/-- Naturality of a Künneth map `(α₁ ⊗ α₂) ≫ μ`, for abstract functors. -/
lemma kunnethMap_naturality_aux (α₁ : ΨM ⋙ s₁ ⟶ g₁ ⋙ ΨP) (α₂ : ΨN ⋙ s₂ ⟶ g₂ ⋙ ΨP)
    (μ : ∀ U V, ΨP.obj U ⊗ ΨP.obj V ⟶ ΨP.obj (U ⊗ V))
    (hμ : ∀ {U U' V V' : CP} (x : U ⟶ U') (y : V ⟶ V'),
      (ΨP.map x ⊗ₘ ΨP.map y) ≫ μ U' V' = μ U V ≫ ΨP.map (x ⊗ₘ y))
    {A A' : CM} {B B' : CN} (a : A ⟶ A') (b : B ⟶ B') :
    ((α₁.app A ⊗ₘ α₂.app B) ≫ μ _ _) ≫ ΨP.map (g₁.map a ⊗ₘ g₂.map b) =
      (s₁.map (ΨM.map a) ⊗ₘ s₂.map (ΨN.map b)) ≫ (α₁.app A' ⊗ₘ α₂.app B') ≫ μ _ _ := by
  have h₁ := α₁.naturality a
  have h₂ := α₂.naturality b
  simp only [Functor.comp_map] at h₁ h₂
  rw [Category.assoc, ← hμ, tensorHom_comp_tensorHom_assoc, ← h₁, ← h₂,
    tensorHom_comp_tensorHom_assoc]

end Abstract

section General

variable {X X' Y Y' Z Z' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {P : NearbyCyclesModel Z Z'} {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}

/-- The Künneth map `Π_{A,B}` is natural in `A` and `B`. -/
lemma kunnethMap_naturality (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    {A A' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    {B B' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))} (a : A ⟶ A') (b : B ⟶ B') :
    kunnethMap Λ φ₁ φ₂ A B ≫
        (P.nearbyCycles Λ).map (L((f₁)^*⟦Λ⟧).map a ⊗ₘ L((f₂)^*⟦Λ⟧).map b) =
      (L((f₁')^*⟦Λ⟧).map ((M.nearbyCycles Λ).map a) ⊗ₘ
          L((f₂')^*⟦Λ⟧).map ((N.nearbyCycles Λ).map b)) ≫ kunnethMap Λ φ₁ φ₂ A' B' := by
  exact kunnethMap_naturality_aux (φ₁.pullbackExchange Λ) (φ₂.pullbackExchange Λ)
    (P.tensorMap Λ) (fun x y ↦ P.tensorMap_natural Λ x y) a b

/-- The Künneth map `Π_{A,B}` is invertible if `Π_{A',B'}` is, for `A ≅ A'` and `B ≅ B'`. -/
lemma isIso_kunnethMap_of_iso (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    {A A' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    {B B' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))} (a : A ≅ A') (b : B ≅ B')
    (h : IsIso (kunnethMap Λ φ₁ φ₂ A' B')) : IsIso (kunnethMap Λ φ₁ φ₂ A B) := by
  have e := kunnethMap_naturality Λ φ₁ φ₂ a.hom b.hom
  have : IsIso (kunnethMap Λ φ₁ φ₂ A B ≫
      (P.nearbyCycles Λ).map (L((f₁)^*⟦Λ⟧).map a.hom ⊗ₘ L((f₂)^*⟦Λ⟧).map b.hom)) := by
    rw [e]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((P.nearbyCycles Λ).map (L((f₁)^*⟦Λ⟧).map a.hom ⊗ₘ L((f₂)^*⟦Λ⟧).map b.hom))

/-- The inclusion `M.geometric ⟶ M` of the geometric model of the total space into a model whose
identification factors as `ε = j ≫ e`, over `e` and `𝟙 X'`. -/
@[simps]
def geometricHom (M : NearbyCyclesModel X X') {e : M.total ⟶ X} (he : M.j ≫ e = M.ε) :
    M.geometric.Hom M e (𝟙 X') where
  total := 𝟙 _
  generic := 𝟙 _
  comm_j := by simp [geometric]
  comm_i := by simp [geometric]
  comm_ε := by simp [geometric, he]

/-- The morphism `M.geometric.toGeneric ⟶ M` of models over `ε` and `𝟙 X'`. -/
@[simps]
def toGenericHom (M : NearbyCyclesModel X X') : M.geometric.toGeneric.Hom M M.ε (𝟙 X') where
  total := 𝟙 _
  generic := 𝟙 _
  comm_j := by simp [geometric]
  comm_i := by simp [geometric]
  comm_ε := by simp [geometric]

/-- A morphism of models `φ : P ⟶ M` induces a morphism
`P.geometric.toGeneric ⟶ M.geometric` over `j_P ≫ φ.total`. -/
@[simps]
def Hom.toGeometricGeneric (φ : P.Hom M f₁ f₁') :
    P.geometric.toGeneric.Hom M.geometric (P.j ≫ φ.total) f₁' where
  total := φ.total
  generic := φ.generic
  comm_j := φ.comm_j
  comm_i := φ.comm_i
  comm_ε := by simpa [geometric] using φ.comm_j

/-- The inclusions of the models of the total spaces are restriction data of the Künneth map. -/
lemma isKunnethRestriction_toGeometricGeneric (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε) :
    IsKunnethRestriction φ₁ φ₂ φ₁.toGeometricGeneric φ₂.toGeometricGeneric (M.geometricHom heM)
      (N.geometricHom heN) P.toGenericHom where
  htot₁ := by simp
  hgen₁ := by simp
  htot₂ := by simp
  hgen₂ := by simp
  hb₁ := by
    simp only [Category.assoc]
    rw [← reassoc_of% φ₁.comm_j, heM, φ₁.comm_ε]
  hs₁ := by simp
  hb₂ := by
    simp only [Category.assoc]
    rw [← reassoc_of% φ₂.comm_j, heN, φ₂.comm_ε]
  hs₂ := by simp
  isOpenImmersion_M := inferInstanceAs (IsOpenImmersion (𝟙 _))
  isOpenImmersion_N := inferInstanceAs (IsOpenImmersion (𝟙 _))
  isOpenImmersion_P := inferInstanceAs (IsOpenImmersion (𝟙 _))
  isPullback_M :=
    have : IsIso (M.geometricHom heM).generic := inferInstanceAs (IsIso (𝟙 _))
    have : IsIso (M.geometricHom heM).total := inferInstanceAs (IsIso (𝟙 _))
    IsPullback.of_horiz_isIso ⟨by simp [geometric]⟩
  isPullback_N :=
    have : IsIso (N.geometricHom heN).generic := inferInstanceAs (IsIso (𝟙 _))
    have : IsIso (N.geometricHom heN).total := inferInstanceAs (IsIso (𝟙 _))
    IsPullback.of_horiz_isIso ⟨by simp [geometric]⟩
  isPullback_P :=
    have : IsIso P.toGenericHom.generic := inferInstanceAs (IsIso (𝟙 _))
    have : IsIso P.toGenericHom.total := inferInstanceAs (IsIso (𝟙 _))
    IsPullback.of_horiz_isIso ⟨by simp [geometric]⟩

/-- **Reduction to the models of the total spaces**: for models whose identifications factor
through the total spaces, `ε_M = j ≫ e_M`, `ε_N = j ≫ e_N`, the Künneth map `Π_{A,B}` is
invertible if the Künneth map `Π_{Le_M^* A, Le_N^* B}` of the models `M.geometric`,
`N.geometric`, `P.geometric.toGeneric` is. -/
theorem isIso_kunnethMap_of_toGeometricGeneric (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (h : IsIso (kunnethMap Λ φ₁.toGeometricGeneric φ₂.toGeometricGeneric
      (L((eM)^*⟦Λ⟧).obj A) (L((eN)^*⟦Λ⟧).obj B))) :
    IsIso (kunnethMap Λ φ₁ φ₂ A B) := by
  have := (isIso_map_kunnethMap_iff_of_isKunnethRestriction Λ
    (isKunnethRestriction_toGeometricGeneric φ₁ φ₂ heM heN) A B).2 h
  exact (NatIso.isIso_map_iff (leftDerivedUpperStarId Λ Z') _).1 this

end General

section Closure

variable {k' : Type u} [Field k']

/-- The closed point `Spec k' ⟶ Spec k'⟦t⟧` is a monomorphism. -/
instance mono_traitClosedPoint : Mono (traitClosedPoint k') := by
  have : IsClosedImmersion (traitClosedPoint k') :=
    IsClosedImmersion.spec_of_surjective _ fun a ↦ ⟨PowerSeries.C a, by simp⟩
  infer_instance

variable {T T' : Scheme.{u}}

/-- The morphism `T ×_S s ⟶ T' ×_S s` of special fibres induced by a morphism `c : T ⟶ T'` of
schemes over the trait. -/
noncomputable def traitStdProjSpecial (q : T ⟶ trait k') (c : T ⟶ T') (q' : T' ⟶ trait k')
    (hc : c ≫ q' = q) : (traitStdSpecialFibre q).left ⟶ (traitStdSpecialFibre q').left :=
  pullback.lift (pullback.fst q (traitClosedPoint k') ≫ c) (pullback.snd _ _)
    (by rw [Category.assoc, hc, pullback.condition])

/-- The morphism of models from the model of the geometric generic fibre of the standard model of
`T` to the geometric standard model of `T'` induced by a morphism `c : T ⟶ T'` over the trait. -/
@[simps]
noncomputable def traitStdProj (q : T ⟶ trait k') (c : T ⟶ T') (q' : T' ⟶ trait k')
    (hc : c ≫ q' = q) :
    (traitStdModel q).geometric.toGeneric.Hom (traitStdModel q').geometric
      (pullback.fst q (traitGenericPoint k') ≫ c) (traitStdProjSpecial q c q' hc) where
  total := c
  generic := pullback.lift (pullback.fst q (traitGenericPoint k') ≫ c) (pullback.snd _ _)
    (by rw [Category.assoc, hc, pullback.condition])
  comm_j := pullback.lift_fst _ _ _
  comm_i := pullback.lift_fst _ _ _
  comm_ε := (pullback.lift_fst _ _ _).trans (Category.id_comp _).symm

variable {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left}

/-- The first projection of the product over the trait of the standard models of `Xc` and `Yc`. -/
noncomputable abbrev closureFst {Xc Yc : Scheme.{u}} (qcM : Xc ⟶ trait k') (qcN : Yc ⟶ trait k') :=
  traitStdProj (pullback.fst qcM qcN ≫ qcM) (pullback.fst qcM qcN) qcM rfl

/-- The second projection of the product over the trait of the standard models of `Xc` and
`Yc`. -/
noncomputable abbrev closureSnd {Xc Yc : Scheme.{u}} (qcM : Xc ⟶ trait k') (qcN : Yc ⟶ trait k') :=
  traitStdProj (pullback.fst qcM qcN ≫ qcM) (pullback.snd qcM qcN) qcN pullback.condition.symm

/-- **Passing to closures**: let `P` be the product over the trait of models `M`, `N` along
`qM`, `qN`, with second projection compatible with the structure morphisms `gM`, `gN` of the
geometric generic fibres, and let `uM : 𝒳 ⟶ Xc`, `uN : 𝒴 ⟶ Yc` be open immersions over the trait
into noetherian schemes. If the Künneth map of the product `Xc ×_S Yc` of the standard models is
invertible on bounded constructible complexes, then so is the Künneth map of the models of the
total spaces of `M`, `N`, `P`. The coefficients are extended by zero along `uM`, `uN`. -/
theorem isIso_kunnethMap_toGeometricGeneric_of_closure {φ₁ : P.Hom M f₁ f₁'}
    {φ₂ : P.Hom N f₂ f₂'} {qM : M.total ⟶ trait k'}
    {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {qN : N.total ⟶ trait k'}
    {gN : N.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hcomp : φ₂.generic ≫ gN = φ₁.generic ≫ gM) {Xc Yc : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace Xc] [TopologicalSpace.NoetherianSpace Yc]
    {qcM : Xc ⟶ trait k'} {qcN : Yc ⟶ trait k'} (uM : M.total ⟶ Xc) (uN : N.total ⟶ Yc)
    [IsOpenImmersion uM] [IsOpenImmersion uN] (huM : uM ≫ qcM = qM) (huN : uN ≫ qcN = qN)
    (hK : ∀ (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Xc) Ab.{u + 1})
        (condensedRingObj Λ Xc)))
      (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Yc) Ab.{u + 1})
        (condensedRingObj Λ Yc))),
      boundedConstructible (condensedRingObj Λ Xc) A →
        boundedConstructible (condensedRingObj Λ Yc) B →
          IsIso (kunnethMap Λ (closureFst qcM qcN) (closureSnd qcM qcN) A B))
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj Λ M.total))}
    (hA : boundedConstructible (condensedRingObj Λ M.total) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.total) Ab.{u + 1})
      (condensedRingObj Λ N.total))}
    (hB : boundedConstructible (condensedRingObj Λ N.total) B) :
    IsIso (kunnethMap Λ φ₁.toGeometricGeneric φ₂.toGeometricGeneric A B) := by
  let uP : P.total ⟶ pullback qcM qcN := pullback.lift (φ₁.total ≫ uM) (φ₂.total ≫ uN)
    (by rw [Category.assoc, Category.assoc, huM, huN, hpb.w])
  have huP : uP ≫ pullback.fst qcM qcN ≫ qcM = φ₁.total ≫ qM := by simp [uP, huM]
  have : IsOpenImmersion uP := by
    have e : uP = hpb.isoPullback.hom ≫ pullback.map qM qN qcM qcN uM uN (𝟙 _) (by simp [huM])
        (by simp [huN]) := by
      apply pullback.hom_ext <;> simp [uP]
    rw [e]
    infer_instance
  have hj₁ : ∀ {W : Scheme.{u}} (x : M.total ⟶ W), φ₁.generic ≫ M.j ≫ x = P.j ≫ φ₁.total ≫ x :=
    fun x ↦ by rw [← Category.assoc, φ₁.comm_j, Category.assoc]
  have hj₂ : ∀ {W : Scheme.{u}} (x : N.total ⟶ W), φ₂.generic ≫ N.j ≫ x = P.j ≫ φ₂.total ≫ x :=
    fun x ↦ by rw [← Category.assoc, φ₂.comm_j, Category.assoc]
  have hi₁ : ∀ {W : Scheme.{u}} (x : M.total ⟶ W), f₁' ≫ M.i ≫ x = P.i ≫ φ₁.total ≫ x :=
    fun x ↦ by rw [← Category.assoc, φ₁.comm_i, Category.assoc]
  have hi₂ : ∀ {W : Scheme.{u}} (x : N.total ⟶ W), f₂' ≫ N.i ≫ x = P.i ≫ φ₂.total ≫ x :=
    fun x ↦ by rw [← Category.assoc, φ₂.comm_i, Category.assoc]
  have hZ₁ : f₁' ≫ X'.hom = Z'.hom := by
    rw [← cancel_mono (traitClosedPoint k'), Category.assoc, ← hM.isPullback_i.w, hi₁,
      hP.isPullback_i.w]
  have hZ₂ : f₂' ≫ Y'.hom = Z'.hom := by
    rw [← cancel_mono (traitClosedPoint k'), Category.assoc, ← hN.isPullback_i.w, hi₂, ← hpb.w,
      hP.isPullback_i.w]
  have hR : IsKunnethRestriction (closureFst qcM qcN) (closureSnd qcM qcN) φ₁.toGeometricGeneric
      φ₂.toGeometricGeneric (traitStdHom qcM hM.isPullback_j hM.isPullback_i uM huM)
      (traitStdHom qcN hN.isPullback_j hN.isPullback_i uN huN)
      (traitStdHom _ hP.isPullback_j hP.isPullback_i uP huP).toGeneric :=
    { htot₁ := by simp [uP]
      hgen₁ := by apply pullback.hom_ext <;> simp [uP, hj₁]
      htot₂ := by simp [uP]
      hgen₂ := by apply pullback.hom_ext <;> simp [uP, hj₂, hcomp]
      hb₁ := by simp [uP]
      hs₁ := by
        apply pullback.hom_ext <;>
          simp [uP, traitStdSpecialHom, traitStdProjSpecial, hi₁, hZ₁]
      hb₂ := by simp [uP]
      hs₂ := by
        apply pullback.hom_ext <;>
          simp [uP, traitStdSpecialHom, traitStdProjSpecial, hi₂, hZ₂]
      isOpenImmersion_M := inferInstanceAs (IsOpenImmersion uM)
      isOpenImmersion_N := inferInstanceAs (IsOpenImmersion uN)
      isOpenImmersion_P := inferInstanceAs (IsOpenImmersion uP)
      isPullback_M := isPullback_traitStdHom_generic qcM hM.isPullback_j hM.isPullback_i uM huM
      isPullback_N := isPullback_traitStdHom_generic qcN hN.isPullback_j hN.isPullback_i uN huN
      isPullback_P := isPullback_traitStdHom_generic _ hP.isPullback_j hP.isPullback_i uP huP }
  have hA' := boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj Λ uM A hA
  have hB' := boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj Λ uN B hB
  have := hK _ _ hA' hB'
  have h := (isIso_map_kunnethMap_iff_of_isKunnethRestriction Λ hR
    (D((uM)_!open⟦Λ⟧).obj A) (D((uN)_!open⟦Λ⟧).obj B)).1 inferInstance
  exact isIso_kunnethMap_of_iso Λ _ _
    (asIso ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ uM).unit.app A))
    (asIso ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ uN).unit.app B)) h

end Closure

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
