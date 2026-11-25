/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethLocal
public import WeilConjectures.TraceFormula.Specialization.TraitModelRestrict
public import WeilConjectures.TraceFormula.Specialization.TraitProduct

/-!

# Restricting products over the trait to opens of the total spaces

Let `P` be the product over the trait `S = Spec k'⟦t⟧` of models `M`, `N` of finite type over
`S` (`NearbyCyclesModel.IsTraitProduct`), with total spaces `𝒳`, `𝒴` and `𝒵 = 𝒳 ×_S 𝒴`. This file
restricts the product to opens `V ⊆ 𝒳`, `W ⊆ 𝒴`:

* the restriction `M.restrictOpen V` of a model to an open `V` of its total space
  (`NearbyCyclesModel.restrictOpen`) is again of finite type over the trait
  (`NearbyCyclesModel.IsTraitModelOver.restrictOpen`);
* the restriction `φ.restrictOpen U V` of a morphism of models to opens `U`, `V` of the total
  spaces with `U ⊆ φ⁻¹ V` (`NearbyCyclesModel.Hom.restrictOpen`);
* the restrictions of `P` to `U = pr₁⁻¹ V ∩ pr₂⁻¹ W = V ×_S W` with the restricted projections form
  a product over the trait of the restrictions of `M` and `N`
  (`NearbyCyclesModel.IsTraitProduct.restrictOpen`), and the inclusions are restriction data of
  the Künneth map in the sense of `NearbyCyclesModel.IsKunnethRestriction`
  (`NearbyCyclesModel.isKunnethRestriction_restrictOpen`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k']

/-- If `a ≫ b = c ≫ d` and `U ⊆ b⁻¹ V`, then `a⁻¹ U ⊆ c⁻¹ (d⁻¹ V)`. -/
lemma preimage_le_preimage_of_comm {A B C D : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C}
    {d : C ⟶ D} (w : a ≫ b = c ≫ d) {U : B.Opens} {V : D.Opens} (h : U ≤ b ⁻¹ᵁ V) :
    a ⁻¹ᵁ U ≤ c ⁻¹ᵁ (d ⁻¹ᵁ V) := fun x hx ↦ by
  change d (c x) ∈ V
  rw [← Scheme.Hom.comp_apply, ← w, Scheme.Hom.comp_apply]
  exact h hx

/-- **Opens of a fibre product**: for a cartesian square `𝒵 = 𝒳 ×_S 𝒴` and opens `V ⊆ 𝒳`,
`W ⊆ 𝒴`, the open `pr₁⁻¹ V ∩ pr₂⁻¹ W` of `𝒵` is the fibre product `V ×_S W`. -/
lemma isPullback_resLE_inf {Z X Y S : Scheme.{u}} {f₁ : Z ⟶ X} {f₂ : Z ⟶ Y} {q₁ : X ⟶ S}
    {q₂ : Y ⟶ S} (h : IsPullback f₁ f₂ q₁ q₂) (V : X.Opens) (W : Y.Opens) :
    IsPullback (f₁.resLE V (f₁ ⁻¹ᵁ V ⊓ f₂ ⁻¹ᵁ W) inf_le_left)
      (f₂.resLE W (f₁ ⁻¹ᵁ V ⊓ f₂ ⁻¹ᵁ W) inf_le_right) (V.ι ≫ q₁) (W.ι ≫ q₂) := by
  set U := f₁ ⁻¹ᵁ V ⊓ f₂ ⁻¹ᵁ W
  have hw : f₁.resLE V U inf_le_left ≫ V.ι ≫ q₁ = f₂.resLE W U inf_le_right ≫ W.ι ≫ q₂ := by
    simp only [Scheme.Hom.resLE_comp_ι_assoc, h.w]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw (fun s ↦ IsOpenImmersion.lift U.ι
      (h.lift (s.fst ≫ V.ι) (s.snd ≫ W.ι) (by simpa using s.condition)) ?_) ?_ ?_ ?_)
  · rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · change f₁ _ ∈ V
      rw [← Scheme.Hom.comp_apply, h.lift_fst, Scheme.Hom.comp_apply]
      exact (s.fst x).2
    · change f₂ _ ∈ W
      rw [← Scheme.Hom.comp_apply, h.lift_snd, Scheme.Hom.comp_apply]
      exact (s.snd x).2
  · intro s
    rw [← cancel_mono V.ι]
    simp
  · intro s
    rw [← cancel_mono W.ι]
    simp
  · intro s m h₁ h₂
    rw [← cancel_mono U.ι, IsOpenImmersion.lift_fac]
    refine h.hom_ext ?_ ?_
    · rw [h.lift_fst, Category.assoc, ← Scheme.Hom.resLE_comp_ι (e := inf_le_left),
        reassoc_of% h₁]
    · rw [h.lift_snd, Category.assoc, ← Scheme.Hom.resLE_comp_ι (e := inf_le_right),
        reassoc_of% h₂]

section Restrict

variable {X : Scheme.{u}} {X' : Over (Spec (.of k'))}

/-- The restriction of a model of finite type over the trait along `q`, `g` to an open `V` of
its total space with quasi-compact inclusion is of finite type over the trait along the
restrictions of `q` and `g`. -/
lemma IsTraitModelOver.restrictOpen {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g)
    (V : M.total.Opens) [QuasiCompact V.ι] :
    (M.restrictOpen V).IsTraitModelOver (X' := M.restrictSpecialFibre V) (V.ι ≫ q)
      ((M.j ⁻¹ᵁ V).ι ≫ g) := by
  have := hM.locallyOfFiniteType
  have := hM.quasiCompact
  have := hM.isSeparated
  exact ⟨inferInstanceAs (LocallyOfFiniteType (V.ι ≫ q)),
    inferInstanceAs (QuasiCompact (V.ι ≫ q)), inferInstanceAs (IsSeparated (V.ι ≫ q)),
    (isPullback_morphismRestrict M.j V).paste_vert hM.isPullback_j,
    (isPullback_morphismRestrict M.i V).paste_vert hM.isPullback_i⟩

end Restrict

section HomRestrict

variable {X Y : Scheme.{u}} {X' Y' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {f : X ⟶ Y} {f' : X'.left ⟶ Y'.left}

/-- The restriction `f'|: i_M⁻¹ U ⟶ i_N⁻¹ V` of the morphism of special fibres of a morphism of
models, for opens `U ⊆ φ⁻¹ V` of the total spaces. -/
noncomputable def Hom.restrictOpenSpecial (φ : M.Hom N f f') (U : M.total.Opens)
    (V : N.total.Opens) (hUV : U ≤ φ.total ⁻¹ᵁ V) :
    (M.restrictSpecialFibre U).left ⟶ (N.restrictSpecialFibre V).left :=
  f'.resLE (N.i ⁻¹ᵁ V) (M.i ⁻¹ᵁ U) (preimage_le_preimage_of_comm φ.comm_i.symm hUV)

/-- The restriction of a morphism of models `φ : M ⟶ N` to opens `U ⊆ φ⁻¹ V` of the total
spaces. -/
@[simps]
noncomputable def Hom.restrictOpen (φ : M.Hom N f f') (U : M.total.Opens) (V : N.total.Opens)
    (hUV : U ≤ φ.total ⁻¹ᵁ V) :
    (M.restrictOpen U).Hom (N.restrictOpen V) f (φ.restrictOpenSpecial U V hUV) where
  total := φ.total.resLE V U hUV
  generic := φ.generic.resLE (N.j ⁻¹ᵁ V) (M.j ⁻¹ᵁ U)
    (preimage_le_preimage_of_comm φ.comm_j.symm hUV)
  comm_j := by
    rw [← cancel_mono V.ι]
    simp [φ.comm_j]
  comm_i := by
    rw [← cancel_mono V.ι]
    simp [restrictOpenSpecial, φ.comm_i]
  comm_ε := by simp [φ.comm_ε]

end HomRestrict

section Product

variable {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left}

/-- The open `pr₁⁻¹ V ∩ pr₂⁻¹ W = V ×_S W` of the total space of a product. -/
abbrev productOpen (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂') (V : M.total.Opens)
    (W : N.total.Opens) : P.total.Opens :=
  φ₁.total ⁻¹ᵁ V ⊓ φ₂.total ⁻¹ᵁ W

/-- **Restriction of a product over the trait**: the restrictions of the projections of a
product over the trait to `V ×_S W` exhibit it as the product of the restrictions to `V`
and `W`. -/
theorem IsTraitProduct.restrictOpen {φ₁ : P.Hom M f₁ f₁'} {φ₂ : P.Hom N f₂ f₂'}
    (h : IsTraitProduct φ₁ φ₂) (V : M.total.Opens) (W : N.total.Opens) [QuasiCompact V.ι]
    [QuasiCompact W.ι] [QuasiCompact (productOpen φ₁ φ₂ V W).ι] :
    IsTraitProduct (X' := M.restrictSpecialFibre V) (Y' := N.restrictSpecialFibre W)
      (Z' := P.restrictSpecialFibre (productOpen φ₁ φ₂ V W))
      (φ₁.restrictOpen (productOpen φ₁ φ₂ V W) V inf_le_left)
      (φ₂.restrictOpen (productOpen φ₁ φ₂ V W) W inf_le_right) := by
  obtain ⟨qM, gM, qN, gN, hM, hN, hpb, hP, hc⟩ := h.exists_isTraitModelOver
  obtain ⟨eM, heM⟩ := h.exists_comp_ε_left
  obtain ⟨eN, heN⟩ := h.exists_comp_ε_right
  refine ⟨⟨V.ι ≫ qM, (M.j ⁻¹ᵁ V).ι ≫ gM, W.ι ≫ qN, (N.j ⁻¹ᵁ W).ι ≫ gN, hM.restrictOpen V,
    hN.restrictOpen W, isPullback_resLE_inf hpb V W, ?_, ?_⟩, ⟨V.ι ≫ eM, ?_⟩, ⟨W.ι ≫ eN, ?_⟩⟩
  · convert hP.restrictOpen (productOpen φ₁ φ₂ V W) using 1 <;>
      simp [Scheme.Hom.resLE_comp_ι_assoc]
  · simp [Scheme.Hom.resLE_comp_ι_assoc, hc]
  · simp [← heM]
  · simp [← heN]

/-- The inclusions of the restrictions of a product to `V ×_S W`, `V` and `W` are restriction
data of the Künneth map along open immersions with cartesian squares of geometric generic
fibres. -/
theorem isKunnethRestriction_restrictOpen (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (V : M.total.Opens) (W : N.total.Opens) :
    IsKunnethRestriction φ₁ φ₂ (φ₁.restrictOpen (productOpen φ₁ φ₂ V W) V inf_le_left)
      (φ₂.restrictOpen (productOpen φ₁ φ₂ V W) W inf_le_right) (M.restrictOpenHom V)
      (N.restrictOpenHom W) (P.restrictOpenHom (productOpen φ₁ φ₂ V W)) where
  htot₁ := Scheme.Hom.resLE_comp_ι _ _
  hgen₁ := Scheme.Hom.resLE_comp_ι _ _
  htot₂ := Scheme.Hom.resLE_comp_ι _ _
  hgen₂ := Scheme.Hom.resLE_comp_ι _ _
  hb₁ := by simp
  hs₁ := Scheme.Hom.resLE_comp_ι _ _
  hb₂ := by simp
  hs₂ := Scheme.Hom.resLE_comp_ι _ _
  isOpenImmersion_M := inferInstanceAs (IsOpenImmersion V.ι)
  isOpenImmersion_N := inferInstanceAs (IsOpenImmersion W.ι)
  isOpenImmersion_P := inferInstanceAs (IsOpenImmersion (productOpen φ₁ φ₂ V W).ι)
  isPullback_M := (isPullback_morphismRestrict M.j V).flip
  isPullback_N := (isPullback_morphismRestrict N.j W).flip
  isPullback_P := (isPullback_morphismRestrict P.j _).flip

end Product

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
