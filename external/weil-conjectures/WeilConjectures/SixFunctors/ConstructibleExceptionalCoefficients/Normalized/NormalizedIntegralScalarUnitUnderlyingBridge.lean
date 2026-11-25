/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData
public import WeilConjectures.FourierTransform.CompletedLineTensor.CompletedLineTensorCoherence
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.CompletedScalarIdentityUnitNormalization

/-! # Bridge from a normalized scalar identity to the completed unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

private theorem inclusion_obj_model (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : FieldStage.{max u v} l) (T : Scheme.{max u v})
    (K : C.{u, v} l Ω T (.integral E)) :
    (RingStage.inclusion.{u, v} l Ω T (.integral E)).obj K = K.obj := rfl

private theorem inclusion_map_model (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : FieldStage.{max u v} l) (T : Scheme.{max u v})
    (K L : C.{u, v} l Ω T (.integral E)) (f : K ⟶ L) :
    HEq ((RingStage.inclusion.{u, v} l Ω T (.integral E)).map f) f.hom := HEq.rfl

private theorem unit_hom_model (l : ℕ) [Fact l.Prime]
    (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{w})
    (K : DerivedCategory (integralTowerModules l E T))
    (hK : IsDerivedCompleteUnrestricted l E T K) :
    (CompletedLineTensor.unit l E T K hK).hom =
      (CompletedLineTensor.chi l E T E (AlgHom.id (Padic l) E) K hK).inv ≫
        (CompletedLineTensor.ordinaryUnit l E T).hom.app K := rfl

private theorem normalized_comparison {D : Type*} [Category D] {A B C X Y : D}
    (r : A ≅ B) (χ : C ≅ X) (hBC : B = C) (hAX : A = X)
    (n : B ⟶ Y) (j : C ⟶ Y) (f : A ⟶ Y)
    (hc : HEq r.inv χ.hom) (hj : HEq n j) (hn : f = r.hom ≫ n) :
    HEq f (χ.inv ≫ j) := by
  subst C
  subst X
  have hr : r.hom = χ.inv := by
    apply (cancel_epi r.inv).1
    rw [r.inv_hom_id, eq_of_heq hc, χ.hom_inv_id]
  rw [hn, hr, eq_of_heq hj]

private theorem scalar_identity_equation (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {s : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l)}
    (h : ∀ W : Scheme.{max u v}, a.map W = 𝟙 _)
    (T : Scheme.{max u v}) (S : Scalar.{u, v} l Ω a T)
    (e : ScalarIdentity.{u, v} l Ω h T S) (K : C.{u, v} l Ω T (s.stage l)) :
    (RingStage.inclusion.{u, v} l Ω T s).map (e.iso.hom.app K) =
      S.realization.hom.app K ≫
        normalizedScalarIdentityArrow (congrArg pbcDerivedExtend (h T))
          (PurCompactSupport.tensorIdentity ((s.coefficients l).ring T))
          ((RingStage.inclusion.{u, v} l Ω T s).obj K) := by
  cases a with
  | mk amap asquare =>
    have hm : amap = (fun W ↦ 𝟙 (((s.coefficients l).ring W))) := funext h
    subst amap
    have hn := e.normalized K
    simp only [normalizedScalarIdentityArrow, eqToIso_refl,
      Iso.refl_hom, NatTrans.id_app, Category.id_comp] at hn ⊢
    erw [Category.id_comp] at hn
    exact hn

attribute [local irreducible] normalizedScalarIdentityArrow

private theorem stage_arrow_normalization (l : ℕ) [Fact l.Prime]
    (E : FieldStage.{w} l) (T : Scheme.{w})
    (ha : (PurCompactSupport.completedChange l E.carrier E.carrier
      (AlgHom.id (Padic l) E.carrier)).map T = 𝟙 _)
    (K : DerivedCategory (integralTowerModules l E.carrier T)) :
    HEq (normalizedScalarIdentityArrow (congrArg (pbcDerivedExtend (X := T)
        (R := (RingStage.coefficients l (RingStage.integral E)).ring T)
        (S := (RingStage.coefficients l (RingStage.integral E)).ring T)) ha)
      (PurCompactSupport.tensorIdentity
        ((RingStage.coefficients l (RingStage.integral E)).ring T)) K)
      ((CompletedLineTensor.ordinaryUnit l E.carrier T).hom.app K) := by
  dsimp only [RingStage.coefficients]
  exact completed_scalar_identity_arrow_normalization l E.carrier T ha K

private theorem stage_extension_eq (l : ℕ) [Fact l.Prime]
    (E : FieldStage.{w} l) (T : Scheme.{w}) :
    (pbcDerivedExtend (X := T)
        (R := (RingStage.coefficients l (RingStage.integral E)).ring T)
        (S := (RingStage.coefficients l (RingStage.integral E)).ring T))
      ((PurCompactSupport.completedChange l E.carrier E.carrier
        (AlgHom.id (Padic l) E.carrier)).map T) =
      completedDerivedScalarExtension l E.carrier E.carrier
        (AlgHom.id (Padic l) E.carrier) T := by
  dsimp only [RingStage.coefficients]
  exact completed_scalar_identity_extension_eq l E.carrier T

private theorem functor_obj_eq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (h : F = G) (K : C) : F.obj K = G.obj K :=
  congrArg (fun F ↦ F.obj K) h

/-- The normalized restricted identity agrees with the completed tensor unit.
Source: exceptional coefficient construction, integral identity clause; Stacks Project,
Tags 03DA, 06YY and 07A6.
(blueprint: lem-sf-normalized-integral-scalar-unit-underlying-bridge)

Proof: use the normalization equation for `e`. The scalar-object equality supplied by
`hS` identifies its source with the completed scalar extension. The inverse realization
hypothesis `hχ` identifies the realization map with the inverse comparison `chi.inv`.
The ordinary K-flat multiplication computation identifies the transported tensor unit
with `CompletedLineTensor.unit`; substituting these equalities into `e.normalized`
gives the displayed heterogeneous equality. -/
theorem normalized_integral_scalar_unit_underlying_bridge
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : FieldStage.{max u v} l) (T : Scheme.{max u v})
    (S : Scalar.{u, v} l Ω (s := .integral E) (t := .integral E)
      (PurCompactSupport.completedChange l E.carrier E.carrier
        (AlgHom.id (Padic l) E.carrier)) T)
    (hS : S.functor ⋙ RingStage.inclusion.{u, v} l Ω T (.integral E) =
      RingStage.inclusion.{u, v} l Ω T (.integral E) ⋙
        integralScalarExtensionOfUniverses l E.carrier E.carrier
          (AlgHom.id (Padic l) E.carrier) T)
    (hχ : ∀ K : C.{u, v} l Ω T (.integral E),
      HEq (S.realization.inv.app K)
        ((completedScalarComparison l E.carrier E.carrier
          (AlgHom.id (Padic l) E.carrier) T).app K.obj))
    (h : ∀ W : Scheme.{max u v},
      (PurCompactSupport.completedChange l E.carrier E.carrier
        (AlgHom.id (Padic l) E.carrier)).map W = 𝟙 _)
    (e : ScalarIdentity.{u, v} l Ω h T S)
    (K : C.{u, v} l Ω T (.integral E)) :
    HEq ((e.iso.hom.app K).hom)
      ((CompletedLineTensor.unit l E.carrier T K.obj
        (CompletedLineTensor.intrinsic_complete l E.carrier T
          ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier T).obj K))).hom) := by
  let hK := CompletedLineTensor.intrinsic_complete l E.carrier T
    ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier T).obj K)
  let χ := CompletedLineTensor.chi l E.carrier T E.carrier
    (AlgHom.id (Padic l) E.carrier) K.obj hK
  let I := RingStage.inclusion.{u, v} l Ω T (.integral E)
  have hobj := inclusion_obj_model l Ω E T K
  have hfg := stage_extension_eq l E T
  have hu := stage_arrow_normalization l E T (h T) K.obj
  have hc : HEq (S.realization.inv.app K) χ.hom := by
    unfold χ CompletedLineTensor.chi
    simp only [asIso_hom]
    exact hχ K
  have hn := scalar_identity_equation l Ω h T S e K
  have hBC := (functor_obj_eq hfg (I.obj K)).trans
    (congrArg (fun Q ↦ (completedDerivedScalarExtension l E.carrier E.carrier
      (AlgHom.id (Padic l) E.carrier) T).obj Q) hobj)
  have hAX := (functor_obj_eq hS K).trans
    (congrArg (fun Q ↦ (integralScalarExtensionOfUniverses l E.carrier E.carrier
      (AlgHom.id (Padic l) E.carrier) T).obj Q) hobj)
  have hres := normalized_comparison (S.realization.app K) χ hBC hAX
    _ _ (I.map (e.iso.hom.app K)) hc hu hn
  have hleft := inclusion_map_model l Ω E T (S.functor.obj K) K (e.iso.hom.app K)
  have hright := unit_hom_model l E.carrier T K.obj hK
  exact hleft.symm.trans (hres.trans (heq_of_eq hright.symm))

end WeilConjectures.ConstructibleExceptionalCoefficients
