/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.CurryIsoCriterion
public import WeilConjectures.WeilSheaf.IhomCurry
public import WeilConjectures.WeilSheaf.SplitTorsor

/-!
# Pairings of isotypic components of pushforwards along split torsors

Let `π : W ⟶ Z` be a quasi-compact surjective weakly étale morphism and `τ_g`, `g ∈ G`,
automorphisms of `W` over `Z` splitting `π` (`AlgebraicGeometry.ProEtale.IsTorsorSplit`), `G` a
finite abelian group whose order is invertible in `ℚ̄_ℓ`. The group acts on `P = π_* ℚ̄_ℓ`
(`AlgebraicGeometry.ProEtale.torsorTranslation`) by ring automorphisms, `P` being a commutative
ring object (the sheaf of functions on the fibres of `π`).

* For a character `χ` of `G`, `e_χ = |G|⁻¹ ∑_g χ(-g) σ_g`
  (`AlgebraicGeometry.ProEtale.torsorIdempotent`) projects onto the `χ`-isotypic component, and a
  morphism `φ : M ⟶ P` on which `G` acts through `χ` and whose adjoint `π^* M ⟶ ℚ̄_ℓ` is an
  isomorphism is split by a retraction `r` with `r ≫ φ = e_χ`
  (`AlgebraicGeometry.ProEtale.exists_retraction_of_isotypic`).
* Given such `φᵢ : Mᵢ ⟶ P` of types `χ₁`, `χ₂` and `χ₁ χ₂`, the product of functions induces a
  pairing `M₁ ⊗ M₂ ⟶ M₃` (`AlgebraicGeometry.ProEtale.torsorPairing`) which after pullback along
  `π` is the multiplication of `ℚ̄_ℓ` (`AlgebraicGeometry.ProEtale.torsorPairing_upperStar`), so
  that its curried form `M₁ ⟶ 𝓗om(M₂, M₃)` is an isomorphism
  (`AlgebraicGeometry.ProEtale.isIso_torsorPairingCurry`).

This is the descent argument behind the multiplicativity `ℒ_{ψ,f} ⊗ ℒ_{ψ,g} ≅ ℒ_{ψ,f+g}` of the
Artin–Schreier sheaves (blueprint `lemma-artin-schreier-character-sheaf`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped Obj

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

/-- If the `ev_i` are jointly monomorphic, `F φ ≫ ev_i = θ ≫ s_i` with `θ` invertible and
`F e ≫ ev_i = a ≫ s_i`, then `F e` factors through `F φ`. -/
lemma Functor.map_eq_comp_of_jointlyMono {ι : Type*} {P M : C} {U : D}
    (ev : ι → (F.obj P ⟶ U))
    (hev : ∀ {T : D} (a b : T ⟶ F.obj P), (∀ i, a ≫ ev i = b ≫ ev i) → a = b)
    (s : ι → (U ⟶ U)) (e : P ⟶ P) (a : F.obj P ⟶ U) (φ : M ⟶ P) (θ : F.obj M ⟶ U) [IsIso θ]
    (he : ∀ i, F.map e ≫ ev i = a ≫ s i) (hφ : ∀ i, F.map φ ≫ ev i = θ ≫ s i) :
    F.map e = a ≫ CategoryTheory.inv θ ≫ F.map φ :=
  hev _ _ fun i ↦ by
    rw [he, Category.assoc, Category.assoc, hφ i, IsIso.inv_hom_id_assoc]

/-- With `F` faithful and additive and `s_{i₀} = 𝟙`, `φ` is a monomorphism and `e` factors
through it. -/
lemma Functor.mono_and_comp_cokernel_eq_zero_of_jointlyMono [Abelian C] [Preadditive D]
    [F.Additive] [F.Faithful] {ι : Type*} {P M : C} {U : D} (ev : ι → (F.obj P ⟶ U))
    (hev : ∀ {T : D} (a b : T ⟶ F.obj P), (∀ i, a ≫ ev i = b ≫ ev i) → a = b)
    (s : ι → (U ⟶ U)) (i₀ : ι) (hs : s i₀ = 𝟙 U) (e : P ⟶ P) (a : F.obj P ⟶ U) (φ : M ⟶ P)
    (θ : F.obj M ⟶ U) [IsIso θ]
    (he : ∀ i, F.map e ≫ ev i = a ≫ s i) (hφ : ∀ i, F.map φ ≫ ev i = θ ≫ s i) :
    Mono φ ∧ e ≫ cokernel.π φ = 0 := by
  have h := F.map_eq_comp_of_jointlyMono ev hev s e a φ θ he hφ
  refine ⟨?_, F.map_injective ?_⟩
  · have : Mono (F.map φ) := by
      have hsplit : F.map φ ≫ ev i₀ ≫ CategoryTheory.inv θ = 𝟙 _ := by
        rw [← Category.assoc, hφ, hs, Category.comp_id, IsIso.hom_inv_id]
      exact (IsSplitMono.mk' ⟨_, hsplit⟩).mono
    exact F.mono_of_mono_map this
  · rw [F.map_comp, h, Category.assoc, Category.assoc, ← F.map_comp, cokernel.condition,
      F.map_zero, Functor.map_zero, comp_zero, comp_zero]

end CategoryTheory

namespace CategoryTheory

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory C]
  [MonoidalCategory D] [MonoidalCategory E]

/-- The component at a monoid of a monoidal natural transformation out of a composite of lax
monoidal functors is a morphism of monoids, the source being `G (F A)`. -/
lemma NatTrans.isMonHom_app_comp {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [F.LaxMonoidal]
    [G.LaxMonoidal] [H.LaxMonoidal] (α : F ⋙ G ⟶ H) [NatTrans.IsMonoidal α] (A : C)
    [MonObj A] : IsMonHom (α.app A) := by
  have h := NatTrans.isMonHom_app α A
  constructor
  · have := h.one_hom
    simp only [Functor.obj.η_def, Functor.LaxMonoidal.comp_ε, Functor.comp_map,
      Category.assoc] at this ⊢
    exact this
  · have := h.mul_hom
    simp only [Functor.obj.μ_def, Functor.LaxMonoidal.comp_μ, Functor.comp_map,
      Category.assoc] at this ⊢
    exact this



/-- The component at a monoid of a monoidal natural transformation into a composite of lax
monoidal functors is a morphism of monoids, the target being `G (F A)`. -/
lemma NatTrans.isMonHom_app_comp_right {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [F.LaxMonoidal]
    [G.LaxMonoidal] [H.LaxMonoidal] (α : H ⟶ F ⋙ G) [NatTrans.IsMonoidal α] (A : C)
    [MonObj A] : IsMonHom (α.app A) := by
  have h := NatTrans.isMonHom_app α A
  constructor
  · have := h.one_hom
    simp only [Functor.obj.η_def, Functor.LaxMonoidal.comp_ε, Functor.comp_map,
      Category.assoc] at this ⊢
    simp
  · have := h.mul_hom
    simp only [Functor.obj.μ_def, Functor.LaxMonoidal.comp_μ, Functor.comp_map,
      Category.assoc] at this ⊢
    simp

/-- For a monoidal adjunction `F ⊣ G` and a monoid `B`, the adjoint of the product
`(f₁ ⊗ f₂) ≫ μ ≫ G.map mul` of two morphisms into `G B` is the product of their adjoints. -/
lemma Adjunction.map_tensorHom_mul_comp_counit {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [F.OplaxMonoidal] [G.LaxMonoidal] [adj.IsMonoidal] {X₁ X₂ : C} {B : D} [MonObj B]
    (f₁ : X₁ ⟶ G.obj B) (f₂ : X₂ ⟶ G.obj B) :
    F.map ((f₁ ⊗ₘ f₂) ≫ μ G B B ≫ G.map (MonObj.mul (X := B))) ≫ adj.counit.app B =
      δ F X₁ X₂ ≫ ((F.map f₁ ≫ adj.counit.app B) ⊗ₘ (F.map f₂ ≫ adj.counit.app B)) ≫
        MonObj.mul (X := B) := by
  rw [F.map_comp, F.map_comp, Category.assoc, Category.assoc]
  erw [adj.counit_naturality]
  rw [
    Adjunction.map_μ_comp_counit_app_tensor_assoc, ← Functor.OplaxMonoidal.δ_natural_assoc,
    tensorHom_comp_tensorHom_assoc]
end CategoryTheory
namespace CategoryTheory.Mod

variable {C : Type*} [Category C] [MonoidalCategory C] {A : C} [MonObj A]

/-- If the action of `A` on the algebra `P` is multiplication through `u : A ⟶ P`, the
action commutes with the multiplication (blueprint `lemma-artin-schreier-character-sheaf`). -/
@[reassoc]
lemma act_whiskerRight_mul {P : Mod C A} [MonObj P.X] (u : A ⟶ P.X)
    (hP : act P.X = u ▷ P.X ≫ MonObj.mul) :
    act P.X ▷ P.X ≫ MonObj.mul = (α_ A P.X P.X).hom ≫ A ◁ MonObj.mul ≫ act P.X := by
  rw [hP, comp_whiskerRight, Category.assoc, MonObj.mul_assoc,
    associator_naturality_left_assoc, whisker_exchange_assoc]

/-- The pairing `(φ₁ ⊗ φ₂) ≫ mul ≫ r` through an `A`-algebra `P` is `A`-linear in the first
variable. -/
lemma pairing_linear_left {P : Mod C A} [MonObj P.X] (u : A ⟶ P.X)
    (hP : act P.X = u ▷ P.X ≫ MonObj.mul) {M₁ M₂ M₃ : Mod C A} (φ₁ : M₁ ⟶ P) (φ₂ : M₂ ⟶ P)
    (r : P ⟶ M₃) :
    act M₁.X ▷ M₂.X ≫ (φ₁.hom ⊗ₘ φ₂.hom) ≫ MonObj.mul ≫ r.hom =
      (α_ A M₁.X M₂.X).hom ≫ A ◁ ((φ₁.hom ⊗ₘ φ₂.hom) ≫ MonObj.mul ≫ r.hom) ≫ act M₃.X := by
  have h1 : act M₁.X ▷ M₂.X ≫ (φ₁.hom ⊗ₘ φ₂.hom) =
      ((𝟙 A ⊗ₘ φ₁.hom) ⊗ₘ φ₂.hom) ≫ act P.X ▷ P.X := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id, act_hom, id_tensorHom]
  rw [reassoc_of% h1, act_whiskerRight_mul_assoc u hP, act_hom, associator_naturality_assoc]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc, id_tensorHom]

variable [BraidedCategory C]

/-- If the action of `A` on the commutative algebra `P` is multiplication through
`u : A ⟶ P`, the action on the second factor commutes with the multiplication
(blueprint `lemma-artin-schreier-character-sheaf`). -/
@[reassoc]
lemma whiskerLeft_act_mul {P : Mod C A} [MonObj P.X] [IsCommMonObj P.X] (u : A ⟶ P.X)
    (hP : act P.X = u ▷ P.X ≫ MonObj.mul) :
    P.X ◁ act P.X ≫ MonObj.mul = (α_ P.X A P.X).inv ≫ (β_ P.X A).hom ▷ P.X ≫
      (α_ A P.X P.X).hom ≫ A ◁ MonObj.mul ≫ act P.X := by
  rw [← act_whiskerRight_mul u hP, hP]
  have hc : P.X ◁ u ≫ MonObj.mul = (β_ P.X A).hom ≫ u ▷ P.X ≫ MonObj.mul := by
    conv_lhs => rw [← IsCommMonObj.mul_comm P.X]
    rw [BraidedCategory.braiding_naturality_right_assoc]
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, MonObj.mul_assoc_flip,
    associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, hc]
  simp only [comp_whiskerRight, Category.assoc]

/-- The pairing `(φ₁ ⊗ φ₂) ≫ mul ≫ r` through a commutative `A`-algebra `P` is `A`-linear in
the second variable. -/
lemma pairing_linear_right {P : Mod C A} [MonObj P.X] [IsCommMonObj P.X] (u : A ⟶ P.X)
    (hP : act P.X = u ▷ P.X ≫ MonObj.mul) {M₁ M₂ M₃ : Mod C A} (φ₁ : M₁ ⟶ P) (φ₂ : M₂ ⟶ P)
    (r : P ⟶ M₃) :
    M₁.X ◁ act M₂.X ≫ (φ₁.hom ⊗ₘ φ₂.hom) ≫ MonObj.mul ≫ r.hom =
      (α_ M₁.X A M₂.X).inv ≫ (β_ M₁.X A).hom ▷ M₂.X ≫ (α_ A M₁.X M₂.X).hom ≫
        A ◁ ((φ₁.hom ⊗ₘ φ₂.hom) ≫ MonObj.mul ≫ r.hom) ≫ act M₃.X := by
  have h1 : M₁.X ◁ act M₂.X ≫ (φ₁.hom ⊗ₘ φ₂.hom) =
      (φ₁.hom ⊗ₘ (𝟙 A ⊗ₘ φ₂.hom)) ≫ P.X ◁ act P.X := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id, act_hom, id_tensorHom]
  rw [reassoc_of% h1, whiskerLeft_act_mul_assoc u hP, act_hom]
  have h2 : ((φ₁.hom ⊗ₘ 𝟙 A) ⊗ₘ φ₂.hom) ≫ (β_ P.X A).hom ▷ P.X =
      (β_ M₁.X A).hom ▷ M₂.X ≫ ((𝟙 A ⊗ₘ φ₁.hom) ⊗ₘ φ₂.hom) := by
    rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      BraidedCategory.braiding_naturality, Category.id_comp, Category.comp_id]
  rw [associator_inv_naturality_assoc, reassoc_of% h2, associator_naturality_assoc]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc, id_tensorHom]

end CategoryTheory.Mod
namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

variable {Z W : Scheme.{u}} (π : W ⟶ Z) {G : Type u} (τ : G → (W ≅ W))
  (hτ : ∀ g, (τ g).hom ≫ π = π) [AddCommGroup G] [Finite G]

variable (l) in
/-- The projector `e_χ = |G|⁻¹ ∑_g χ(-g) σ_g` of `π_* ℚ̄_ℓ` onto its `χ`-isotypic component. -/
noncomputable def torsorIdempotent (χ : AddChar G (PadicAlgCl l)) :
    (π)_*ᵃ[l].obj (AdicSheaf.unit l W) ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W) :=
  letI := Fintype.ofFinite G
  ∑ g : G, AdicSheaf.smul (ULift.up ((Nat.card G : PadicAlgCl l)⁻¹ * χ (-g))) _ ≫
    torsorTranslation l π τ hτ g

omit [AddCommGroup G] [Finite G] in
/-- The underlying morphism of a finite sum of morphisms of `ℓ`-adic sheaves. -/
lemma _root_.CategoryTheory.Mod.hom_sum {ι : Type*} {X : Scheme.{u}} {M N : AdicSheaf l X}
    (s : Finset ι) (f : ι → (M ⟶ N)) : (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom :=
  (Mod.forget _).map_sum f s

/-- A morphism of sheaves on which `G` acts through `χ` is fixed by the projector `e_χ`. -/
lemma comp_torsorIdempotent_hom (χ : AddChar G (PadicAlgCl l))
    (hG : (Nat.card G : PadicAlgCl l) ≠ 0)
    {T : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)}
    (q : T ⟶ ((π)_*ᵃ[l].obj (AdicSheaf.unit l W)).X)
    (hq : ∀ g, q ≫ (torsorTranslation l π τ hτ g).hom =
      (ULift.up (χ g) : ULift (PadicAlgCl l)) • q) :
    q ≫ (torsorIdempotent l π τ hτ χ).hom = q := by
  let := Fintype.ofFinite G
  rw [torsorIdempotent, Mod.hom_sum, Preadditive.comp_sum]
  have (g : G) : q ≫ (AdicSheaf.smul (ULift.up
      ((Nat.card G : PadicAlgCl l)⁻¹ * χ (-g))) _ ≫ torsorTranslation l π τ hτ g).hom =
      (ULift.up ((Nat.card G : PadicAlgCl l)⁻¹) : ULift (PadicAlgCl l)) • q := by
    rw [Mod.comp_hom', AdicSheaf.smul_hom, Linear.smul_comp,
      Category.id_comp, Linear.comp_smul, hq, smul_smul]
    congr 1
    refine ULift.ext ?_
    change (Nat.card G : PadicAlgCl l)⁻¹ * χ (-g) * χ g = _
    rw [mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, mul_one]
  simp_rw [this]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul
    (ULift (PadicAlgCl l)), smul_smul]
  convert one_smul (ULift (PadicAlgCl l)) q
  refine ULift.ext ?_
  change (Nat.card G : PadicAlgCl l) * (Nat.card G : PadicAlgCl l)⁻¹ = 1
  exact mul_inv_cancel₀ hG

/-- A morphism on which `G` acts through `χ` is fixed by the projector `e_χ`. -/
lemma comp_torsorIdempotent (χ : AddChar G (PadicAlgCl l))
    (hG : (Nat.card G : PadicAlgCl l) ≠ 0) {M : AdicSheaf l Z}
    (φ : M ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W))
    (hφ : ∀ g, φ ≫ torsorTranslation l π τ hτ g = AdicSheaf.smul (ULift.up (χ g)) M ≫ φ) :
    φ ≫ torsorIdempotent l π τ hτ χ = φ := by
  refine Mod.hom_ext _ _ ?_
  rw [Mod.comp_hom']
  refine comp_torsorIdempotent_hom π τ hτ χ hG _ fun g ↦ ?_
  rw [← Mod.comp_hom', hφ, Mod.comp_hom', AdicSheaf.smul_hom, Linear.smul_comp, Category.id_comp]

/-- **Isotypic retraction.** -/
theorem exists_retraction_of_isotypic [WeaklyEtale π] [QuasiCompact π] [Surjective π]
    (hadd : ∀ g h, (τ (g + h)).hom = (τ g).hom ≫ (τ h).hom)
    (hsplit : IsTorsorSplit π τ hτ) (χ : AddChar G (PadicAlgCl l))
    (hG : (Nat.card G : PadicAlgCl l) ≠ 0) {M : AdicSheaf l Z}
    (φ : M ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W))
    (hφ : ∀ g, φ ≫ torsorTranslation l π τ hτ g = AdicSheaf.smul (ULift.up (χ g)) M ≫ φ)
    (hθ : IsIso ((π)^*ᵃ[l].map φ ≫ (adicUpperStarLowerStarAdjunction l π).counit.app _)) :
    ∃ r : (π)_*ᵃ[l].obj (AdicSheaf.unit l W) ⟶ M,
      φ ≫ r = 𝟙 M ∧ r ≫ φ = torsorIdempotent l π τ hτ χ := by
  let := Fintype.ofFinite G
  let := Fintype.ofFinite G
  have : (π)^*ᵃ[l].Faithful := AdicSheaf.faithful_upperStar π
  let U := AdicSheaf.unit l W
  let c : G → PadicAlgCl l := fun g ↦ (Nat.card G : PadicAlgCl l)⁻¹ * χ (-g)
  have he (h : G) : (π)^*ᵃ[l].map (torsorIdempotent l π τ hτ χ) ≫ torsorEval l π τ hτ h =
      (∑ g : G, AdicSheaf.smul (ULift.up (c g)) _ ≫ torsorEval l π τ hτ g) ≫
        AdicSheaf.smul (ULift.up (χ h)) U := by
    have e₁ : (π)^*ᵃ[l].map (torsorIdempotent l π τ hτ χ) =
        ∑ g : G, AdicSheaf.smul (ULift.up (c g)) _ ≫
          (π)^*ᵃ[l].map (torsorTranslation l π τ hτ g) := by
      rw [torsorIdempotent, Functor.map_sum]
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      rw [Functor.map_comp, AdicSheaf.adicUpperStar_map_smul]
    rw [e₁, Preadditive.sum_comp, Preadditive.sum_comp]
    simp only [Category.assoc]
    simp_rw [upperStar_map_torsorTranslation_comp_torsorEval _ _ _ hadd]
    conv_rhs => rw [← Equiv.sum_comp (Equiv.addRight h)]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    simp only [Equiv.coe_addRight]
    rw [← AdicSheaf.smul_comp, ← Category.assoc, AdicSheaf.smul_smul]
    have hχ : χ h * χ (-h) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    refine congrArg (fun x : ULift.{u + 1} (PadicAlgCl l) ↦ AdicSheaf.smul x _ ≫ _)
      (ULift.ext ?_)
    change c g = χ h * c (g + h)
    simp only [c, neg_add, AddChar.map_add_eq_mul]
    linear_combination (-((Nat.card G : PadicAlgCl l)⁻¹ * χ (-g))) * hχ
  have hφ' (g : G) : (π)^*ᵃ[l].map φ ≫ torsorEval l π τ hτ g =
      ((π)^*ᵃ[l].map φ ≫ (adicUpperStarLowerStarAdjunction l π).counit.app _) ≫
        AdicSheaf.smul (ULift.up (χ g)) U := by
    rw [torsorEval, ← Functor.map_comp_assoc, hφ g, Functor.map_comp,
      AdicSheaf.adicUpperStar_map_smul, Category.assoc, AdicSheaf.smul_comp]
  obtain ⟨hmono, hcok⟩ := (π)^*ᵃ[l].mono_and_comp_cokernel_eq_zero_of_jointlyMono
    (torsorEval l π τ hτ)
    (fun a b h ↦ Mod.hom_ext _ _ (torsorEval_hom_ext _ _ _ hsplit fun g ↦ by
      rw [← Mod.comp_hom', ← Mod.comp_hom', h g]))
    (fun g ↦ AdicSheaf.smul (ULift.up (χ g)) U) 0
    (by rw [AddChar.map_zero_eq_one]; exact AdicSheaf.smul_one U)
    (torsorIdempotent l π τ hτ χ) _ φ _ he hφ'
  refine ⟨Abelian.monoLift φ _ hcok, ?_, Abelian.monoLift_comp _ _ _⟩
  rw [← cancel_mono φ, Category.assoc, Abelian.monoLift_comp, Category.id_comp,
    comp_torsorIdempotent π τ hτ χ hG φ hφ]


/-- The ring structure of `π_* ℚ̄_ℓ` (functions on the fibres of `π`). -/
noncomputable instance (π : W ⟶ Z) : MonObj ((π)_*ᵃ[l].obj (AdicSheaf.unit l W)).X :=
  inferInstanceAs (MonObj ((π)_*[WeilCoefficients.{u} l].obj (adicConstantSheaf l W)))

/-- `π_* ℚ̄_ℓ` is a commutative ring object. -/
instance (π : W ⟶ Z) : IsCommMonObj ((π)_*ᵃ[l].obj (AdicSheaf.unit l W)).X :=
  inferInstanceAs (IsCommMonObj ((π)_*[WeilCoefficients.{u} l].obj (adicConstantSheaf l W)))

/-- The action of `τ_g` on `π_* ℚ̄_ℓ` is a ring morphism. -/
instance isMonHom_torsorTranslation_hom (g : G) :
    IsMonHom (torsorTranslation l π τ hτ g).hom := by
  have : IsMonHom (adicConstantSheafLowerStarIso l (τ g)).inv :=
    inferInstanceAs (IsMonHom (adicConstantSheafToLowerStar l (τ g).hom))
  have h1 := NatTrans.isMonHom_app_comp (lowerStarComp (WeilCoefficients.{u} l) (τ g).hom π).hom
      (adicConstantSheaf l W)
  have h2 : IsMonHom ((lowerStarCongr (WeilCoefficients.{u} l) (hτ g)).hom.app
      (adicConstantSheaf l W)) :=
    NatTrans.isMonHom_app _ _
  exact inferInstanceAs (IsMonHom ((π)_*[WeilCoefficients.{u} l].map
    (adicConstantSheafLowerStarIso l (τ g)).inv ≫
    (lowerStarComp (WeilCoefficients.{u} l) (τ g).hom π).hom.app (adicConstantSheaf l W) ≫
    (lowerStarCongr (WeilCoefficients.{u} l) (hτ g)).hom.app (adicConstantSheaf l W)))


/-- The underlying morphism of the counit of `g^* ⊣ g_*` on `ℓ`-adic sheaves. -/
lemma adicUpperStarLowerStarAdjunction_counit_app_hom_eq {Y : Scheme.{u}} (g : Y ⟶ Z)
    (N : AdicSheaf l Y) :
    ((adicUpperStarLowerStarAdjunction l g).counit.app N).hom =
      (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).counit.app N.X := by
  rw [adicUpperStarLowerStarAdjunction, Adjunction.modAdjunction_counit_app_hom]

/-- The underlying morphism of the adjoint `π^* M ⟶ ℚ̄_ℓ` of `φ : M ⟶ π_* ℚ̄_ℓ`. -/
lemma adjoint_hom {M : AdicSheaf l Z} (φ : M ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W)) :
    ((π)^*ᵃ[l].map φ ≫ (adicUpperStarLowerStarAdjunction l π).counit.app _).hom =
      (π)^*[WeilCoefficients.{u} l].map φ.hom ≫
        (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) π).counit.app
          (adicConstantSheaf l W) := by
  rw [Mod.comp_hom', adicUpperStar_map_hom, adicUpperStarLowerStarAdjunction_counit_app_hom_eq]
  rfl


variable (l) in
/-- The pairing `M₁ ⊗ M₂ ⟶ M₃` induced by `φ₁ : M₁ ⟶ π_* ℚ̄_ℓ`, `φ₂ : M₂ ⟶ π_* ℚ̄_ℓ` and
`r : π_* ℚ̄_ℓ ⟶ M₃`: the product of functions followed by `r`. -/
noncomputable def torsorPairing {M₁ M₂ M₃ : AdicSheaf l Z}
    (φ₁ : M₁ ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W)) (φ₂ : M₂ ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W))
    (r : (π)_*ᵃ[l].obj (AdicSheaf.unit l W) ⟶ M₃) : M₁.X ⊗ M₂.X ⟶ M₃.X :=
  (φ₁.hom ⊗ₘ φ₂.hom) ≫ MonObj.mul ≫ r.hom

omit [Finite G] in
/-- If `G` acts on `φ₁`, `φ₂` through `χ₁`, `χ₂`, it acts on their product through `χ₁ χ₂`. -/
lemma tensorHom_mul_comp_torsorTranslation {M₁ M₂ : AdicSheaf l Z}
    (φ₁ : M₁ ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W)) (φ₂ : M₂ ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W))
    (χ₁ χ₂ : AddChar G (PadicAlgCl l))
    (hφ₁ : ∀ g, φ₁ ≫ torsorTranslation l π τ hτ g = AdicSheaf.smul (ULift.up (χ₁ g)) M₁ ≫ φ₁)
    (hφ₂ : ∀ g, φ₂ ≫ torsorTranslation l π τ hτ g = AdicSheaf.smul (ULift.up (χ₂ g)) M₂ ≫ φ₂)
    (g : G) :
    ((φ₁.hom ⊗ₘ φ₂.hom) ≫ MonObj.mul) ≫ (torsorTranslation l π τ hτ g).hom =
      (ULift.up ((χ₁ * χ₂) g) : ULift (PadicAlgCl l)) • ((φ₁.hom ⊗ₘ φ₂.hom) ≫ MonObj.mul) := by
  rw [Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, ← Mod.comp_hom',
    ← Mod.comp_hom', hφ₁, hφ₂, Mod.comp_hom', Mod.comp_hom', AdicSheaf.smul_hom,
    AdicSheaf.smul_hom, Linear.smul_comp, Linear.smul_comp, Category.id_comp, Category.id_comp,
    tensorHom_def, MonoidalLinear.smul_whiskerRight, MonoidalLinear.whiskerLeft_smul,
    Linear.smul_comp, Linear.comp_smul, smul_smul, Linear.smul_comp, ← tensorHom_def]
  rfl


/-- **The pullback of the pairing is the multiplication.** After pullback along `π` and
transport along the adjoints `θᵢ : π^* Mᵢ ⟶ ℚ̄_ℓ` of the `φᵢ`, the pairing
`torsorPairing φ₁ φ₂ r` becomes the multiplication of `ℚ̄_ℓ`, provided `r ≫ φ₃ = e_{χ₁χ₂}`. -/
lemma torsorPairing_upperStar (χ₁ χ₂ : AddChar G (PadicAlgCl l))
    (hG : (Nat.card G : PadicAlgCl l) ≠ 0) {M₁ M₂ M₃ : AdicSheaf l Z}
    (φ₁ : M₁ ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W)) (φ₂ : M₂ ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W))
    (φ₃ : M₃ ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W)) (r : (π)_*ᵃ[l].obj (AdicSheaf.unit l W) ⟶ M₃)
    (hφ₁ : ∀ g, φ₁ ≫ torsorTranslation l π τ hτ g = AdicSheaf.smul (ULift.up (χ₁ g)) M₁ ≫ φ₁)
    (hφ₂ : ∀ g, φ₂ ≫ torsorTranslation l π τ hτ g = AdicSheaf.smul (ULift.up (χ₂ g)) M₂ ≫ φ₂)
    (hr : r ≫ φ₃ = torsorIdempotent l π τ hτ (χ₁ * χ₂))
    (θ₁ : (π)^*ᵃ[l].obj M₁ ≅ AdicSheaf.unit l W) (θ₂ : (π)^*ᵃ[l].obj M₂ ≅ AdicSheaf.unit l W)
    (hθ₁ : θ₁.hom = (π)^*ᵃ[l].map φ₁ ≫ (adicUpperStarLowerStarAdjunction l π).counit.app _)
    (hθ₂ : θ₂.hom = (π)^*ᵃ[l].map φ₂ ≫ (adicUpperStarLowerStarAdjunction l π).counit.app _) :
    (θ₁.inv.hom ⊗ₘ θ₂.inv.hom) ≫ μ (π)^*[WeilCoefficients.{u} l] M₁.X M₂.X ≫
      (π)^*[WeilCoefficients.{u} l].map (torsorPairing l π φ₁ φ₂ r) ≫
        ((π)^*ᵃ[l].map φ₃ ≫ (adicUpperStarLowerStarAdjunction l π).counit.app _).hom =
      MonObj.mul (X := adicConstantSheaf l W) := by
  set F := (π)^*[WeilCoefficients.{u} l]
  set ε := (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) π).counit
  have key : F.map (torsorPairing l π φ₁ φ₂ r) ≫
      ((π)^*ᵃ[l].map φ₃ ≫ (adicUpperStarLowerStarAdjunction l π).counit.app _).hom =
      δ F M₁.X M₂.X ≫ (θ₁.hom.hom ⊗ₘ θ₂.hom.hom) ≫ MonObj.mul (X := adicConstantSheaf l W) := by
    rw [adjoint_hom, ← F.map_comp_assoc, torsorPairing, Category.assoc, Category.assoc,
      ← Mod.comp_hom', hr, ← Category.assoc (φ₁.hom ⊗ₘ φ₂.hom),
      comp_torsorIdempotent_hom π τ hτ _ hG _
        (tensorHom_mul_comp_torsorTranslation π τ hτ φ₁ φ₂ χ₁ χ₂ hφ₁ hφ₂), hθ₁, hθ₂,
      adjoint_hom, adjoint_hom]
    exact (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) π).map_tensorHom_mul_comp_counit
      (B := adicConstantSheaf l W) φ₁.hom φ₂.hom
  rw [key, Functor.Monoidal.μ_δ_assoc, tensorHom_comp_tensorHom_assoc, ← Mod.comp_hom',
    ← Mod.comp_hom', Iso.inv_hom_id, Iso.inv_hom_id]
  erw [id_tensorHom_id]
  exact Category.id_comp _


/-- The pairing `torsorPairing φ₁ φ₂ r` is `ℚ̄_ℓ`-linear in the second variable. -/
lemma isLinearRight_torsorPairing {M₁ M₂ M₃ : AdicSheaf l Z}
    (φ₁ : M₁ ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W)) (φ₂ : M₂ ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W))
    (r : (π)_*ᵃ[l].obj (AdicSheaf.unit l W) ⟶ M₃) :
    Mod.IsLinearRight (D := M₂) (N := M₃) (torsorPairing l π φ₁ φ₂ r) :=
  Mod.pairing_linear_right (adicConstantSheafToLowerStar l π) rfl φ₁ φ₂ r

/-- The pairing `torsorPairing φ₁ φ₂ r` is `ℚ̄_ℓ`-linear in the first variable. -/
lemma torsorPairing_linear_left {M₁ M₂ M₃ : AdicSheaf l Z}
    (φ₁ : M₁ ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W)) (φ₂ : M₂ ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W))
    (r : (π)_*ᵃ[l].obj (AdicSheaf.unit l W) ⟶ M₃) :
    Mod.act M₁.X ▷ M₂.X ≫ torsorPairing l π φ₁ φ₂ r =
      (α_ (adicConstantSheaf l Z) M₁.X M₂.X).hom ≫ adicConstantSheaf l Z ◁
        torsorPairing l π φ₁ φ₂ r ≫ Mod.act M₃.X :=
  Mod.pairing_linear_left (adicConstantSheafToLowerStar l π) rfl φ₁ φ₂ r

variable (l) in
/-- The curried pairing `M₁ ⟶ 𝓗om(M₂, M₃)`. -/
noncomputable def torsorPairingCurry {M₁ M₂ M₃ : AdicSheaf l Z}
    (φ₁ : M₁ ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W)) (φ₂ : M₂ ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W))
    (r : (π)_*ᵃ[l].obj (AdicSheaf.unit l W) ⟶ M₃) : M₁ ⟶ (AdicSheaf.ihom M₂).obj M₃ :=
  AdicSheaf.curryHom (torsorPairing l π φ₁ φ₂ r) (isLinearRight_torsorPairing π φ₁ φ₂ r)
    (torsorPairing_linear_left π φ₁ φ₂ r)

/-- **The curried pairing is an isomorphism.** -/
theorem isIso_torsorPairingCurry [WeaklyEtale π] [QuasiCompact π] [Surjective π]
    (χ₁ χ₂ : AddChar G (PadicAlgCl l))
    (hG : (Nat.card G : PadicAlgCl l) ≠ 0) {M₁ M₂ M₃ : AdicSheaf l Z}
    (φ₁ : M₁ ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W)) (φ₂ : M₂ ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W))
    (φ₃ : M₃ ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W)) (r : (π)_*ᵃ[l].obj (AdicSheaf.unit l W) ⟶ M₃)
    (hφ₁ : ∀ g, φ₁ ≫ torsorTranslation l π τ hτ g = AdicSheaf.smul (ULift.up (χ₁ g)) M₁ ≫ φ₁)
    (hφ₂ : ∀ g, φ₂ ≫ torsorTranslation l π τ hτ g = AdicSheaf.smul (ULift.up (χ₂ g)) M₂ ≫ φ₂)
    (hr : r ≫ φ₃ = torsorIdempotent l π τ hτ (χ₁ * χ₂))
    (hθ₁ : IsIso ((π)^*ᵃ[l].map φ₁ ≫ (adicUpperStarLowerStarAdjunction l π).counit.app _))
    (hθ₂ : IsIso ((π)^*ᵃ[l].map φ₂ ≫ (adicUpperStarLowerStarAdjunction l π).counit.app _))
    (hθ₃ : IsIso ((π)^*ᵃ[l].map φ₃ ≫ (adicUpperStarLowerStarAdjunction l π).counit.app _)) :
    IsIso (torsorPairingCurry l π φ₁ φ₂ r) := by
  refine isIso_of_upperStar_uncurry_eq_mul π _
    (asIso ((π)^*ᵃ[l].map φ₁ ≫ (adicUpperStarLowerStarAdjunction l π).counit.app _))
    (asIso ((π)^*ᵃ[l].map φ₂ ≫ (adicUpperStarLowerStarAdjunction l π).counit.app _))
    (asIso ((π)^*ᵃ[l].map φ₃ ≫ (adicUpperStarLowerStarAdjunction l π).counit.app _)) ?_
  rw [torsorPairingCurry, AdicSheaf.curryHom_evaluation]
  exact torsorPairing_upperStar π τ hτ χ₁ χ₂ hG φ₁ φ₂ φ₃ r hφ₁ hφ₂ hr _ _ rfl rfl


/-- The exchange `(e_Z)_* π_* ℚ̄_ℓ ≅ π_* ℚ̄_ℓ` of a pushforward with automorphisms `e_Z`, `e_W`
such that `π ≫ e_Z = e_W ≫ π` is compatible with the products of functions. -/
lemma lowerStarExchange_mul (π : W ⟶ Z) (eZ : Z ≅ Z) (eW : W ≅ W)
    (hc : π ≫ eZ.hom = eW.hom ≫ π) :
    let f := ((lowerStarComp (WeilCoefficients.{u} l) π eZ.hom ≪≫
      lowerStarCongr (WeilCoefficients.{u} l) hc ≪≫
      (lowerStarComp (WeilCoefficients.{u} l) eW.hom π).symm).app (adicConstantSheaf l W) ≪≫
        (π)_*[WeilCoefficients.{u} l].mapIso (adicConstantSheafLowerStarIso l eW)).hom
    (f ⊗ₘ f) ≫ MonObj.mul (X := (π)_*[WeilCoefficients.{u} l].obj (adicConstantSheaf l W)) =
      μ (eZ.hom)_*[WeilCoefficients.{u} l] _ _ ≫ (eZ.hom)_*[WeilCoefficients.{u} l].map
        (MonObj.mul (X := (π)_*[WeilCoefficients.{u} l].obj (adicConstantSheaf l W))) ≫ f := by
  intro f
  have h1 := NatTrans.isMonHom_app_comp (lowerStarComp (WeilCoefficients.{u} l) π eZ.hom).hom
    (adicConstantSheaf l W)
  have h2 : IsMonHom ((lowerStarCongr (WeilCoefficients.{u} l) hc).hom.app
      (adicConstantSheaf l W)) := NatTrans.isMonHom_app _ _
  have h3' := NatTrans.isMonHom_app_comp_right (lowerStarComp (WeilCoefficients.{u} l) eW.hom π).inv
    (adicConstantSheaf l W)
  have : IsMonHom (adicConstantSheafLowerStarIso l eW).inv :=
    inferInstanceAs (IsMonHom (adicConstantSheafToLowerStar l eW.hom))
  have : IsMonHom (adicConstantSheafLowerStarIso l eW).hom := by
    have : IsMonHom (inv (adicConstantSheafLowerStarIso l eW).inv) := inferInstance
    rwa [IsIso.Iso.inv_inv] at this
  have h4 := Functor.map.instIsMonHom (F := (π)_*[WeilCoefficients.{u} l])
    (f := (adicConstantSheafLowerStarIso l eW).hom)
  simp only [f, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.mapIso_hom, Category.assoc]
  rw [← tensorHom_comp_tensorHom_assoc, ← tensorHom_comp_tensorHom_assoc,
    ← tensorHom_comp_tensorHom_assoc, ← IsMonHom.mul_hom, ← IsMonHom.mul_hom_assoc,
    ← IsMonHom.mul_hom_assoc, ← IsMonHom.mul_hom_assoc, Functor.obj.μ_def]
  simp only [Functor.LaxMonoidal.comp_μ, Functor.comp_map, Functor.map_comp, Category.assoc,
    Functor.obj.μ_def]

end AlgebraicGeometry.ProEtale
