/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolutionAlgebraic
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralFinitePointResolutionContinuousSections
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.InternalModuleSectionwiseShortExact

/-! Module-object realization of the lifted continuous-section resolution. -/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CategoryTheory.MonoidalCategory

private abbrev resolutionAb
    (S : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj S

-- Checking linearity on elementary tensors avoids identifying sheaf tensor sections
-- with the tensor product of sections.
private def resolutionModMap
    (R S T : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    (α : resolutionAb R ⟶ resolutionAb S) [IsMonHom α]
    (β : resolutionAb R ⟶ resolutionAb T) [IsMonHom β]
    (k : resolutionAb S ⟶ resolutionAb T)
    (hk : ∀ (P : Profinite.{u}ᵒᵖ) (c : R.obj.obj P) (b : S.obj.obj P),
      k.hom.app P (@Mul.mul (S.obj.obj P) inferInstance (α.hom.app P c) b) =
        @Mul.mul (T.obj.obj P) inferInstance (β.hom.app P c) (k.hom.app P b)) :
    (Mod.comap α).obj (Mod.regular (resolutionAb S)) ⟶
      (Mod.comap β).obj (Mod.regular (resolutionAb T)) := by
  letI : MonObj (resolutionAb S).obj := S.obj.monObjCompForget₂
  letI : MonObj (resolutionAb T).obj := T.obj.monObjCompForget₂
  refine Mod.homMk k ?_
  change (α ▷ _ ≫ MonObj.mul) ≫ k = _ ◁ k ≫ (β ▷ _ ≫ MonObj.mul)
  apply Sheaf.tensor_hom_ext
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc,
    ← Functor.LaxMonoidal.μ_natural_right_assoc,
    ← Functor.LaxMonoidal.μ_natural_left_assoc]
  have hS := Sheaf.μ_comp_map_mul (resolutionAb S)
  have hT := Sheaf.μ_comp_map_mul (resolutionAb T)
  simp only [reassoc_of% hS, hT]
  ext P : 2
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext'
  exact hk P

private def resolutionSectionsEquiv
    (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    (P : Profinite.{u}) (r : ℕ) :
    ULift.{u + 1} C(P, Fin r → PadicAlgCl.integers ell E.1) ≃+
      LiftedPointSections0 ell E P r where
  toFun b := ULift.up ⟨fun x i ↦ ULift.up (b.down x i),
    continuous_pi fun i ↦ continuous_uliftUp.comp
      ((continuous_apply i).comp b.down.continuous)⟩
  invFun b := ULift.up ⟨fun x i ↦ (b.down x i).down,
    continuous_pi fun i ↦ continuous_uliftDown.comp
      ((continuous_apply i).comp b.down.continuous)⟩
  left_inv b := by ext x i; rfl
  right_inv b := by ext x i; rfl
  map_add' b c := by ext x i; rfl

private def resolutionTargetEquiv
    (P : Profinite.{u}) (A : Type u) [TopologicalSpace A] [AddCommGroup A]
    [IsTopologicalAddGroup A] :
    ULift.{u + 1} C(P, A) ≃+ LiftedPointSections2 P A where
  toFun b := ULift.up ⟨fun x ↦ ULift.up (b.down x),
    continuous_uliftUp.comp b.down.continuous⟩
  invFun b := ULift.up ⟨fun x ↦ (b.down x).down,
    continuous_uliftDown.comp b.down.continuous⟩
  left_inv b := by ext x; rfl
  right_inv b := by ext x; rfl
  map_add' b c := by ext x; rfl

private def resolutionDiagonal (O : Type) [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] (r : ℕ) :
    Profinite.continuousMapRingObj.{u} O ⟶
      Profinite.continuousMapRingObj.{u} (Fin r → O) :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat Ab)).map
    (Profinite.continuousMapRingSheafMap (Pi.constRingHom (Fin r) O)
      (continuous_pi fun _ ↦ continuous_id))

private instance resolutionDiagonal_isMonHom (O : Type) [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] (r : ℕ) :
    IsMonHom (resolutionDiagonal.{u} O r) := by
  unfold resolutionDiagonal
  infer_instance

private abbrev resolutionFree (O : Type) [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] (r : ℕ) :=
  (Mod.comap (resolutionDiagonal.{u} O r)).obj
    (Mod.regular (Profinite.continuousMapRingObj.{u} (Fin r → O)))

private def resolutionProjection (O : Type) [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] (r : ℕ) (i : Fin r) :
    resolutionFree.{u} O r ⟶ Mod.regular (Profinite.continuousMapRingObj.{u} O) :=
  resolutionModMap (Profinite.continuousMapRingSheaf O)
    (Profinite.continuousMapRingSheaf (Fin r → O))
    (Profinite.continuousMapRingSheaf O) (resolutionDiagonal O r) (𝟙 _)
    ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat Ab)).map
      (Profinite.continuousMapRingSheafMap (Pi.evalRingHom (fun _ : Fin r ↦ O) i)
        (continuous_apply i)))
    (by intros; rfl) ≫
      (Mod.comapId _).hom.app (Mod.regular (Profinite.continuousMapRingObj O))

private def resolutionInclusion (O : Type) [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] (r : ℕ) (i : Fin r) :
    Mod.regular (Profinite.continuousMapRingObj.{u} O) ⟶ resolutionFree.{u} O r := by
  classical
  let k : Profinite.continuousMapRingObj.{u} O ⟶
      Profinite.continuousMapRingObj.{u} (Fin r → O) :=
    ⟨{ app P := AddCommGrpCat.ofHom
        { toFun b := ULift.up ⟨fun x j ↦ if i = j then b.down x else 0,
            continuous_pi fun j ↦ by
              by_cases h : i = j
              · simpa only [ite_eq_left h] using b.down.continuous
              · simp only [ite_eq_right h]; exact continuous_const⟩
          map_zero' := by
            apply ULift.ext
            ext x j
            simp
          map_add' b c := by
            apply ULift.ext
            ext x j
            change (if i = j then b.down x + c.down x else 0) =
              (if i = j then b.down x else 0) + (if i = j then c.down x else 0)
            by_cases h : i = j <;> simp [h] }
       naturality _ _ _ := by
        ext b
        apply ULift.ext
        ext x j
        rfl }⟩
  refine (Mod.comapId _).inv.app (Mod.regular (Profinite.continuousMapRingObj O)) ≫
    resolutionModMap (Profinite.continuousMapRingSheaf O)
      (Profinite.continuousMapRingSheaf O)
      (Profinite.continuousMapRingSheaf (Fin r → O)) (𝟙 _)
      (resolutionDiagonal O r) k ?_
  intro P c b
  apply ULift.ext
  ext x j
  change (if i = j then c.down x * b.down x else 0) =
    c.down x * (if i = j then b.down x else 0)
  split_ifs <;> simp

private def resolutionFreeIso (O : Type) [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] (r : ℕ) :
    resolutionFree.{u} O r ≅ biproduct
      (fun _ : Fin r ↦ Mod.regular (Profinite.continuousMapRingObj.{u} O)) := by
  classical
  let b : Bicone (fun _ : Fin r ↦
      Mod.regular (Profinite.continuousMapRingObj.{u} O)) :=
    { pt := resolutionFree O r
      π := resolutionProjection O r
      ι := resolutionInclusion O r
      ι_π i j := by
        by_cases h : i = j
        · subst j
          simp only [dite_true, eqToHom_refl]
          apply Mod.hom_ext
          ext P c
          apply ULift.ext
          ext x
          change (if i = i then c.down x else 0) = c.down x
          simp
        · rw [dite_eq_right h]
          apply Mod.hom_ext
          ext P c
          apply ULift.ext
          ext x
          change (if i = j then c.down x else 0) = 0
          simp [h] }
  refine biproduct.uniqueUpToIso _ (b := b) (isBilimitOfTotal b ?_)
  apply Mod.hom_ext
  ext P c
  apply ULift.ext
  ext x j
  let ev : (b.pt ⟶ b.pt) →+ O :=
    { toFun z := ((z.hom.hom.app P) c).down x j
      map_zero' := rfl
      map_add' _ _ := rfl }
  change ev (∑ i : Fin r, b.π i ≫ b.ι i) = ev (𝟙 b.pt)
  rw [map_sum]
  change (∑ i : Fin r, if i = j then c.down x i else 0) = c.down x j
  simp

/-- Shortcut instance: on v4.35 the default search for this instance times out. -/
local instance (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell) :
    ContinuousSMul (PadicAlgCl.integers ell E.1) (PadicAlgCl.integers ell E.1) :=
  ContinuousMul.to_continuousSMul

/-- Shortcut instance: on v4.35 the default search for this instance times out. -/
local instance (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell) :
    ContinuousSMul (PadicAlgCl.integers ell E.1) (ULift.{u + 1} (PadicAlgCl.integers ell E.1)) :=
  ContinuousSMul.induced
    (ULift.moduleEquiv : ULift.{u + 1} (PadicAlgCl.integers ell E.1) ≃ₗ[_] _)

-- Exactness under a change of coordinates is independent of the concrete section types.
private lemma resolution_conjugate_exact
    {X Y X' Y' : Type*} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup X'] [AddCommGroup Y'] (e : X ≃+ X') (d : Y ≃+ Y')
    (F : X' →+ X') (G : X' →+ Y') (h : Function.Exact F G) :
    Function.Exact (fun b ↦ e.symm (F (e b))) (fun b ↦ d.symm (G (e b))) := by
  intro b
  constructor
  · intro hb
    have hb' : G (e b) = 0 := by
      apply d.symm.injective
      simpa only [map_zero] using hb
    obtain ⟨c, hc⟩ := (h _).1 hb'
    refine ⟨e.symm c, ?_⟩
    change e.symm (F (e (e.symm c))) = b
    rw [AddEquiv.apply_symm_apply, hc, AddEquiv.symm_apply_apply]
  · rintro ⟨c, rfl⟩
    change d.symm (G (e (e.symm (F (e c))))) = 0
    rw [AddEquiv.apply_symm_apply, (h _).2 ⟨e c, rfl⟩, map_zero]

private lemma resolution_conjugate_zero
    {X Y X' Y' : Type*} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup X'] [AddCommGroup Y'] (e : X ≃+ X') (d : Y ≃+ Y')
    (F : X' →+ X') (G : X' →+ Y') (h : Function.Exact F G) (b : X) :
    d.symm (G (e (e.symm (F (e b))))) = 0 :=
  (resolution_conjugate_exact e d F G h _).2 ⟨b, rfl⟩

set_option linter.unusedVariables false in
-- The supplied section family subsumes the retained scalar-continuity hypothesis.
/-- Realize a sectionwise exact lifted resolution as a short exact point-module complex.

Source: the sectionwise short-exact criterion, finite-coordinate biproduct comparison, and
pointwise normalization of the scalar map
(blueprint: lem-s3-integral-finite-point-resolution-continuous).
-/
theorem integralFinitePointResolution_continuous_realization
    (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    (A : Type u) [CommRing A] [Finite A]
    (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
      ⟨cartesianFinitePointRing A⟩)
    (φ : PadicAlgCl.integers ell E.1 →+* A)
    (hφ : @Continuous _ _ inferInstance ⊥ φ)
    (hsection : ∀ (P : Profinite.{u})
      (s : ULift.{u + 1} C(P, PadicAlgCl.integers ell E.1)) (x : P),
      ((a.hom.hom.hom.app (op P)) s).down x = φ (s.down x)) :
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := discreteTopology_bot A
    letI : IsTopologicalRing A := inferInstance
    letI : Module (PadicAlgCl.integers ell E.1) A := Module.compHom A φ
    let φ' : PadicAlgCl.integers ell E.1 →+* ULift.{u + 1} A :=
      ULift.ringEquiv.symm.toRingHom.comp φ
    letI : Module (PadicAlgCl.integers ell E.1) (ULift.{u + 1} A) :=
      Module.compHom (ULift.{u + 1} A) φ'
    ∀ (r : ℕ)
      (f : ModuleCat.of.{u + 1} (PadicAlgCl.integers ell E.1)
        (Fin r → ULift.{u + 1} (PadicAlgCl.integers ell E.1)) ⟶
        ModuleCat.of.{u + 1} (PadicAlgCl.integers ell E.1)
          (Fin r → ULift.{u + 1} (PadicAlgCl.integers ell E.1)))
      (g : ModuleCat.of.{u + 1} (PadicAlgCl.integers ell E.1)
        (Fin r → ULift.{u + 1} (PadicAlgCl.integers ell E.1)) ⟶
        ModuleCat.of.{u + 1} (PadicAlgCl.integers ell E.1) (ULift.{u + 1} A)),
      Function.Injective f.hom → Function.Exact f.hom g.hom →
        Function.Surjective g.hom →
      (∃ (F : ∀ P : Profinite.{u},
          LiftedPointSections0 ell E P r →+
            LiftedPointSections0 ell E P r)
        (G : ∀ P : Profinite.{u},
          LiftedPointSections0 ell E P r →+
            LiftedPointSections2 P A),
        (∀ (P : Profinite.{u}) (b : LiftedPointSections0 ell E P r) (s : P),
          (F P b).down s = f.hom (b.down s)) ∧
        (∀ (P : Profinite.{u}) (b : LiftedPointSections0 ell E P r) (s : P),
          (G P b).down s = g.hom (b.down s)) ∧
        (∀ {P Q : Profinite.{u}} (q : C(Q, P))
          (b : LiftedPointSections0 ell E P r),
          (F Q (ULift.up (b.down.comp q))).down = (F P b).down.comp q) ∧
        (∀ {P Q : Profinite.{u}} (q : C(Q, P))
          (b : LiftedPointSections0 ell E P r),
          (G Q (ULift.up (b.down.comp q))).down = (G P b).down.comp q) ∧
        (∀ (P : Profinite.{u}) (c : C(P, PadicAlgCl.integers ell E.1))
          (b : LiftedPointSections0 ell E P r) (s : P),
          (F P (ULift.up (c • b.down))).down s = c s • (F P b).down s) ∧
        (∀ (P : Profinite.{u}) (c : C(P, PadicAlgCl.integers ell E.1))
          (b : LiftedPointSections0 ell E P r) (s : P),
          (G P (ULift.up (c • b.down))).down s = c s • (G P b).down s) ∧
        (∀ P, Function.Injective (F P)) ∧
        (∀ P, Function.Exact (F P) (G P)) ∧
        (∀ P, Function.Surjective (G P))) →
      ∃ (P : ShortComplex (IntegralFiniteScalar.PointModules
          (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}))),
        P.ShortExact ∧
        Nonempty (P.X₁ ≅ biproduct
          (fun _ : Fin r ↦ Mod.regular (Profinite.padicIntegersRingObj ell E.1))) ∧
        Nonempty (P.X₂ ≅ biproduct
          (fun _ : Fin r ↦ Mod.regular (Profinite.padicIntegersRingObj ell E.1))) ∧
        Nonempty (P.X₃ ≅ (Mod.comap a.hom.hom).obj
          (Mod.regular (cartesianFinitePointRing A))) := by
  classical
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := discreteTopology_bot A
  let : IsTopologicalRing A := inferInstance
  let : Module (PadicAlgCl.integers ell E.1) A := Module.compHom A φ
  let φ' : PadicAlgCl.integers ell E.1 →+* ULift.{u + 1} A :=
    ULift.ringEquiv.symm.toRingHom.comp φ
  let : Module (PadicAlgCl.integers ell E.1) (ULift.{u + 1} A) :=
    Module.compHom (ULift.{u + 1} A) φ'
  dsimp only
  intro r f g _hf _hex _hg hFG
  obtain ⟨F, G, hF, hG, _hFn, _hGn, hFs, hGs, hFi, hEx, hGu⟩ := hFG
  let O := PadicAlgCl.integers ell E.1
  let R := Profinite.padicIntegersCondensedRing.{u} ell E.1
  let S := Profinite.continuousMapRingSheaf.{u} (Fin r → O)
  let T := Profinite.continuousCoefficientRingSheaf A
  let M := resolutionFree.{u} O r
  let N := (Mod.comap a.hom.hom).obj (Mod.regular (cartesianFinitePointRing A))
  let e := fun P ↦ resolutionSectionsEquiv ell E P r
  let d := fun P ↦ resolutionTargetEquiv P A
  let FF : resolutionAb S ⟶ resolutionAb S :=
    ⟨{ app P := AddCommGrpCat.ofHom
        ((e P.unop).symm.toAddMonoidHom.comp ((F P.unop).comp
          (e P.unop).toAddMonoidHom))
       naturality P Q q := by
        ext b
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        funext i
        change ((F Q.unop (e Q.unop (ULift.up
          (b.down.comp q.unop.hom.hom)))).down x i).down =
          ((F P.unop (e P.unop b)).down (q.unop.hom.hom x) i).down
        exact congrArg (fun v ↦ (v i).down)
          ((hF Q.unop (e Q.unop (ULift.up (b.down.comp q.unop.hom.hom))) x).trans
            (hF P.unop (e P.unop b) (q.unop.hom.hom x)).symm) }⟩
  let GG : resolutionAb S ⟶ resolutionAb T :=
    ⟨{ app P := AddCommGrpCat.ofHom
        ((d P.unop).symm.toAddMonoidHom.comp ((G P.unop).comp
          (e P.unop).toAddMonoidHom))
       naturality P Q q := by
        ext b
        apply ULift.ext
        ext x
        change ((G Q.unop (e Q.unop (ULift.up
          (b.down.comp q.unop.hom.hom)))).down x).down =
          ((G P.unop (e P.unop b)).down (q.unop.hom.hom x)).down
        exact congrArg ULift.down
          ((hG Q.unop (e Q.unop (ULift.up (b.down.comp q.unop.hom.hom))) x).trans
            (hG P.unop (e P.unop b) (q.unop.hom.hom x)).symm) }⟩
  let FM : M ⟶ M := resolutionModMap R S S (resolutionDiagonal O r)
    (resolutionDiagonal O r) FF (by
      intro P c b
      apply ULift.ext
      apply ContinuousMap.ext
      intro x
      funext i
      exact congrArg (fun v ↦ (v i).down) (hFs P.unop c.down (e P.unop b) x))
  let GM : M ⟶ N := resolutionModMap R S T (resolutionDiagonal O r)
    a.hom.hom GG (by
      intro P c b
      apply ULift.ext
      ext x
      have h := congrArg ULift.down (hGs P.unop c.down (e P.unop b) x)
      change ((G P.unop (e P.unop _)).down x).down =
          ((a.hom.hom.hom.app P) c).down x *
            ((G P.unop (e P.unop b)).down x).down
      rw [hsection]
      exact h)
  have hzero : FM ≫ GM = 0 := by
    apply Mod.hom_ext
    ext P b
    exact resolution_conjugate_zero (e P.unop) (d P.unop)
      (F P.unop) (G P.unop) (hEx P.unop) b
  let C := ShortComplex.mk FM GM hzero
  have hC : C.ShortExact := by
    let U := Mod.forget (D := Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (Profinite.padicIntegersRingObj ell E.1)
    let V := sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
    let B := (C.map U).map V
    have hB (P : Profinite.{u}ᵒᵖ) :
        (B.map ((evaluation _ Ab.{u + 1}).obj P)).ShortExact := by
      have hi : Function.Injective (B.f.app P) :=
        (e P.unop).symm.injective.comp ((hFi P.unop).comp (e P.unop).injective)
      have hu : Function.Surjective (B.g.app P) :=
        (d P.unop).symm.surjective.comp ((hGu P.unop).comp (e P.unop).surjective)
      have hx : Function.Exact (B.f.app P) (B.g.app P) :=
        resolution_conjugate_exact (e P.unop) (d P.unop)
          (F P.unop) (G P.unop) (hEx P.unop)
      exact ShortComplex.ShortExact.mk' ((ShortComplex.ab_exact_iff_function_exact _).2 hx)
        ((AddCommGrpCat.mono_iff_injective _).2 hi)
        ((AddCommGrpCat.epi_iff_surjective _).2 hu)
    exact (Mod.shortExact_of_sectionwise (coherentTopology Profinite.{u})
      (Profinite.padicIntegersRingObj ell E.1) C (fun P ↦ hB (op P))).2.2
  exact ⟨C, hC, ⟨resolutionFreeIso O r⟩, ⟨resolutionFreeIso O r⟩, ⟨Iso.refl _⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
