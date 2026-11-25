/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackSiteData
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientCoefficientPullbackFiniteIso
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! Componentwise sequence-site coefficient pullback.
Source: Stacks 03CB and 0941.
(blueprint: lem-sf-ambient-coefficient-pullback-iso-sequence-app).

The finite-stage comparisons are evaluated on each object of the product site.
Their compatible inverses give the componentwise inverse of the sequence map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.AmbientPullbackTensor
private theorem isIso_of_transpose_in_fullyFaithful_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ C) (G : B ⥤ D) (hF : F.FullyFaithful) (hG : G.FullyFaithful)
    {P : B ⥤ A} {Q : D ⥤ C} {L : A ⥤ B} {l : C ⥤ D}
    (adj : L ⊣ P) (a : l ⊣ Q) (e : P ⋙ F ≅ G ⋙ Q)
    {R : A} {S : B} (η : R ⟶ P.obj S)
    [IsIso ((a.homEquiv _ _).symm (F.map η ≫ e.hom.app S))] :
    IsIso ((adj.homEquiv _ _).symm η) := by
  let γ := (a.homEquiv _ _).symm (F.map η ≫ e.hom.app S)
  apply isIso_of_coyoneda_map_bijective
  intro T
  let b : (S ⟶ T) ≃ (F.obj R ⟶ Q.obj (G.obj T)) :=
    hG.homEquiv |>.trans (Iso.homCongr (asIso γ).symm (Iso.refl _)) |>.trans
      (a.homEquiv _ _)
  let c : (R ⟶ P.obj T) ≃ (F.obj R ⟶ Q.obj (G.obj T)) :=
    hF.homEquiv |>.trans (Iso.homCongr (Iso.refl _) (e.app T))
  have heq : (fun x : S ⟶ T ↦
      c ((adj.homEquiv _ _) ((adj.homEquiv _ _).symm η ≫ x))) = b := by
    funext x
    simp only [b, c, Equiv.trans_apply, Iso.homCongr_apply,
      Iso.symm_inv, asIso_hom, Iso.refl_hom, Iso.refl_inv,
      Functor.FullyFaithful.homEquiv_apply, Category.id_comp, Category.comp_id]
    rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply,
      a.homEquiv_naturality_right]
    simp only [γ, Equiv.apply_symm_apply, CategoryTheory.Functor.map_comp, Category.assoc]
    have hn := e.hom.naturality x
    change F.map (P.map x) ≫ (e.app T).hom =
      e.hom.app S ≫ Q.map (G.map x) at hn
    exact congrArg (fun z ↦ F.map η ≫ z) hn
  have hb : Function.Bijective (fun x : S ⟶ T ↦
      c ((adj.homEquiv _ _) ((adj.homEquiv _ _).symm η ≫ x))) := by
    rw [heq]
    exact b.bijective
  exact ((adj.homEquiv _ _).bijective.of_comp_iff' _).mp
    ((c.bijective.of_comp_iff' _).mp hb)

private local instance levelContinuous (X : Scheme.{t}) (n : ℕ) :
    (Prod.sectR n X.ProEt).IsContinuous (Scheme.ProEt.topology X) (topology X none) := by
  have : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} X.ProEt
  exact SemilinearSections.evaluationContinuous.{t + 1, t, t + 1}
    (Scheme.ProEt.topology X) n

private def levelFunctor (X : Scheme.{t}) :
    Sheaf (topology X none) CommRingCat.{max u (t + 1)} ⥤
      (ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)}) where
  obj H :=
    { obj := fun n ↦ ⟨(Prod.sectR n.unop X.ProEt).op ⋙ H.obj,
        (((Prod.sectR n.unop X.ProEt).sheafPushforwardContinuous
          CommRingCat (Scheme.ProEt.topology X) (topology X none)).obj H).property⟩
      map := fun a ↦
        ⟨{ app := fun U ↦ H.obj.map (Prod.mkHom a.unop (𝟙 U.unop)).op
           naturality := fun U V b ↦ by
             dsimp
             rw [← H.obj.map_comp, ← H.obj.map_comp]
             congr 1 }⟩
      map_id := fun n ↦ by
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext U
        exact H.obj.map_id _
      map_comp := fun a b ↦ by
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext U
        change H.obj.map _ = H.obj.map _ ≫ H.obj.map _
        rw [← H.obj.map_comp]
        apply congrArg H.obj.map
        apply Quiver.Hom.unop_inj
        ext <;> simp }
  map α :=
    { app := fun n ↦ ⟨Functor.whiskerLeft (Prod.sectR n.unop X.ProEt).op α.hom⟩
      naturality := fun n m a ↦ by
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext U
        exact α.hom.naturality _ }

private def levelFunctorFullyFaithful (X : Scheme.{t}) :
    (levelFunctor.{t, u} X).FullyFaithful := by
  let G := (Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (sheafToPresheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)})
  apply Functor.FullyFaithful.ofCompFaithful (G := G)
  let P := (Functor.whiskeringLeft _ _ CommRingCat.{max u (t + 1)}).obj
    (prodOpEquiv (C := ℕ) (D := X.ProEt)).inverse
  have hP : P.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful P
  have h := ((fullyFaithfulSheafToPresheaf (topology X none)
    CommRingCat.{max u (t + 1)}).comp hP).comp Functor.fullyFaithfulCurry
  exact h.ofIso (Iso.refl _)

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]

private def coefficientLevels (X : Scheme.{t}) :
    coefficientSequenceCommRingSystem ell E X ≅
      (levelFunctor.{t, u} X).obj (coefficients ell E X none) :=
  NatIso.ofComponents (fun n ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ Iso.refl _) (by
      intro U V a
      change _ ≫ 𝟙 _ = 𝟙 _ ≫
        ((coefficientSequenceCommRingSystem ell E X).map (𝟙 n)).hom.app U ≫ _
      rw [CategoryTheory.Functor.map_id]
      simp [Prod.sectR]))) (by
    intro n m a
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _ ≫
      (integralCoefficientCommRingSheaf ell E X m.unop).obj.map (𝟙 U)
    rw [CategoryTheory.Functor.map_id]
    simp [Prod.sectR])

private def pushLevels {X Y : Scheme.{t}} (f : X ⟶ Y)
    (H : Sheaf (topology X none) CommRingCat.{max u (t + 1)}) :
    (levelFunctor.{t, u} Y).obj ((ringPush f none).obj H) ≅
      (levelFunctor.{t, u} X).obj H ⋙ ringPush f (some 0) :=
  NatIso.ofComponents (fun n ↦ Iso.refl _) (by
    intro n m a
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    change H.obj.map (Prod.mkHom a.unop
      ((Scheme.proEtaleBaseChange f).map (𝟙 U.unop))).op ≫ 𝟙 _ =
        𝟙 _ ≫ H.obj.map (Prod.mkHom a.unop (𝟙 _)).op
    rw [CategoryTheory.Functor.map_id]
    simp)

/-- Every component of the sequence coefficient pullback is invertible.

Source: Stacks 03CB and 0941 (finite/sequence coefficient comparison).
Proof: evaluate the sequence-site adjunction at a product object `(n,U)`.  The
component is the finite-stage coefficient comparison at index `n`; its inverse
is the finite-stage inverse transported along the product projection.  The
finite inverses commute with all quotient transition maps, so they assemble to
a morphism on the sequence site and satisfy both inverse equations componentwise.
(blueprint: lem-sf-ambient-coefficient-pullback-iso-sequence-app) -/
theorem coefficientPullback_none_isIso_app {X Y : Scheme.{t}}
    (f : X ⟶ Y) (U : Site X none) :
    IsIso ((ringMap ell E f none).hom.app (op U)) := by
  let F := levelFunctor.{t, u} Y
  let G := levelFunctor.{t, u} X
  let P : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)} ⥤
      Sheaf (Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)} :=
    ringPush.{t, u} f (some 0)
  let : P.IsRightAdjoint := ringPushRightAdjoint f (some 0)
  let a := (Adjunction.ofIsRightAdjoint P).whiskerRight ℕᵒᵖ
  let e : ringPush.{t, u} f none ⋙ F ≅
      G ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj P :=
    NatIso.ofComponents (pushLevels f) (by
      intro H K β
      apply NatTrans.ext
      funext n
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      rfl)
  let cX := coefficientLevels ell E X
  let cY := coefficientLevels ell E Y
  let η := ringUnit ell E f none
  let δ : coefficientSequenceCommRingSystem ell E Y ⟶
      coefficientSequenceCommRingSystem ell E X ⋙ P :=
    cY.hom ≫ F.map η ≫ e.hom.app (coefficients ell E X none) ≫
      Functor.whiskerRight cX.inv P
  let α := (a.homEquiv _ _).symm δ
  have hδ (n : ℕ) : δ.app (op n) = ringUnit ell E f (some n) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    dsimp [δ, cX, cY, coefficientLevels, F, G, levelFunctor, η, e, pushLevels]
    simp only [Category.id_comp]
    rfl
  have hα (n : ℕ) : α.app (op n) = ringMap ell E f (some n) := by
    change P.leftAdjoint.map (δ.app (op n)) ≫
      (Adjunction.ofIsRightAdjoint P).counit.app _ = _
    rw [hδ]
    rfl
  have : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    rw [show α.app n = ringMap ell E f (some n.unop) from hα n.unop]
    exact coefficientPullback_some_isIso ell E f n.unop
  let γ := (a.homEquiv _ _).symm
    (F.map η ≫ e.hom.app (coefficients ell E X none))
  have hαγ : α =
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P.leftAdjoint).map cY.hom ≫
        γ ≫ cX.inv := by
    dsimp only [α, δ]
    rw [← Category.assoc (F.map η) (e.hom.app _) _,
      a.homEquiv_naturality_left_symm]
    congr 1
    exact a.homEquiv_naturality_right_symm
      (F.map η ≫ e.hom.app (coefficients ell E X none)) cX.inv
  have hγ : γ =
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P.leftAdjoint).map cY.inv ≫
        α ≫ cX.hom := by
    rw [hαγ]
    simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, Category.comp_id]
  have : IsIso γ := by
    rw [hγ]
    infer_instance
  have : IsIso (ringMap ell E f none) :=
    isIso_of_transpose_in_fullyFaithful_square F G
      (levelFunctorFullyFaithful Y) (levelFunctorFullyFaithful X)
      (Adjunction.ofIsRightAdjoint (ringPush.{t, u} f none)) a e η
  have : IsIso ((sheafToPresheaf (topology X none)
      CommRingCat.{max u (t + 1)}).map (ringMap ell E f none)) := inferInstance
  exact inferInstanceAs (IsIso
    (((sheafToPresheaf (topology X none) CommRingCat.{max u (t + 1)}).map
      (ringMap ell E f none)).app (op U)))

end WeilConjectures.AmbientPullbackTensor
