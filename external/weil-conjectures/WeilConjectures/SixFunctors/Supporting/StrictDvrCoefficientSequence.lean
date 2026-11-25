/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.CategoryTheory.Constant.ConstantFiniteFreeSectionBasis
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralProjectionDivisibility
import all WeilConjectures.Algebra.Homology.ProEtaleCoefficients.SuccessiveQuotientFlatTensorSequence

/-! # The residue-kernel coefficient sequence

Source: Stacks Project, Tag 0942, proof of lemma-bounded (1), elementary DVR sequence
and constant realization, together with Modules on Sites Tags 093J and 03CY.
(blueprint: lem-sf-strict-dvr-coefficient-sequence)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u v r

open CategoryTheory CategoryTheory.Limits Opposite

namespace StrictDvrCoefficientProof

variable {A : Type u} [CommRing A] (π : A)

private abbrev powerIdeal (n : ℕ) : Ideal A := Ideal.span {π} ^ n

private theorem power_mul_mem (n : ℕ) {x : A} (hx : x ∈ powerIdeal π 1) :
    π ^ n * x ∈ powerIdeal π (n + 1) := by
  change π ^ n * x ∈ Ideal.span {π} ^ (n + 1)
  rw [pow_succ]
  exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton π)) n)
    (by simpa only [powerIdeal, pow_one] using hx)

private def residueInjection (n : ℕ) :
    A ⧸ powerIdeal π 1 →ₗ[A] A ⧸ powerIdeal π (n + 1) :=
  (powerIdeal π 1).mapQ (powerIdeal π (n + 1)) (LinearMap.mulLeft A (π ^ n))
    (fun _x hx ↦ power_mul_mem π n hx)

private theorem residueInjection_mk (n : ℕ) (x : A) :
    residueInjection π n (Ideal.Quotient.mk (powerIdeal π 1) x) =
      Ideal.Quotient.mk (powerIdeal π (n + 1)) (π ^ n * x) := rfl

private theorem residueInjection_injective [IsDomain A] (hπ : π ≠ 0) (n : ℕ) :
    Function.Injective (residueInjection π n) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [residueInjection_mk, Ideal.Quotient.eq_zero_iff_mem, powerIdeal,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, hy⟩ := hx
  rw [Ideal.Quotient.eq_zero_iff_mem, powerIdeal, pow_one, Ideal.mem_span_singleton]
  refine ⟨y, mul_left_cancel₀ (pow_ne_zero n hπ) ?_⟩
  simpa only [pow_succ, mul_assoc] using hy

private def powerQuotient (n : ℕ) :
    A ⧸ powerIdeal π (n + 1) →ₗ[A] A ⧸ powerIdeal π n :=
  (powerIdeal π (n + 1)).mapQ (powerIdeal π n) LinearMap.id
    (Ideal.pow_le_pow_right (Nat.le_succ n))

private theorem powerQuotient_mk (n : ℕ) (x : A) :
    powerQuotient π n (Ideal.Quotient.mk (powerIdeal π (n + 1)) x) =
      Ideal.Quotient.mk (powerIdeal π n) x := rfl

private theorem residueSequence_zero (n : ℕ) :
    (powerQuotient π n).comp (residueInjection π n) = 0 := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro x
  change Ideal.Quotient.mk (powerIdeal π n) (π ^ n * x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _
    (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton π)) n)

private theorem powerQuotient_surjective (n : ℕ) :
    Function.Surjective (powerQuotient π n) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk (powerIdeal π (n + 1)) x, rfl⟩

private theorem residueSequence_exact (n : ℕ) :
    Function.Exact (residueInjection π n) (powerQuotient π n) := by
  intro x
  constructor
  · intro hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [powerQuotient_mk, Ideal.Quotient.eq_zero_iff_mem, powerIdeal,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨Ideal.Quotient.mk (powerIdeal π 1) y, ?_⟩
    rw [residueInjection_mk, hy]
  · rintro ⟨y, rfl⟩
    exact DFunLike.congr_fun (residueSequence_zero π n) y

private def residueRingQuotient (n : ℕ) :
    A ⧸ powerIdeal π (n + 1) →+* A ⧸ powerIdeal π 1 :=
  Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.succ_le_succ (Nat.zero_le n))

private theorem residueInjection_mul (n : ℕ)
    (a : A ⧸ powerIdeal π (n + 1)) (x : A ⧸ powerIdeal π 1) :
    residueInjection π n (residueRingQuotient π n a * x) = a * residueInjection π n x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change residueInjection π n (Ideal.Quotient.mk (powerIdeal π 1) (a * x)) =
    Ideal.Quotient.mk (powerIdeal π (n + 1)) a *
      residueInjection π n (Ideal.Quotient.mk (powerIdeal π 1) x)
  rw [residueInjection_mk, residueInjection_mk, ← map_mul]
  congr 1
  exact mul_left_comm _ _ _

private def liftRingHom {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    ULift.{t} R →+* ULift.{t} S :=
  ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom)

private abbrev liftedResidue (n : ℕ) : ModuleCat.{max u t} (ULift.{t} (A ⧸ powerIdeal π (n + 1))) :=
  letI := (liftRingHom.{t, u} (residueRingQuotient π n)).toAlgebra
  ModuleCat.of (ULift.{t} (A ⧸ powerIdeal π (n + 1))) (ULift.{t} (A ⧸ powerIdeal π 1))

private abbrev liftedTarget (n : ℕ) : ModuleCat.{max u t} (ULift.{t} (A ⧸ powerIdeal π (n + 1))) :=
  letI := (liftRingHom.{t, u}
    (Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.le_succ n))).toAlgebra
  ModuleCat.of (ULift.{t} (A ⧸ powerIdeal π (n + 1))) (ULift.{t} (A ⧸ powerIdeal π n))

private def liftedInjection (n : ℕ) :
    liftedResidue.{t, u} π n ⟶ ModuleCat.of
      (ULift.{t} (A ⧸ powerIdeal π (n + 1))) (ULift.{t} (A ⧸ powerIdeal π (n + 1))) :=
  letI : Module (ULift.{t} (A ⧸ powerIdeal π (n + 1)))
      (liftedResidue.{t, u} π n) := (liftedResidue.{t, u} π n).isModule
  ModuleCat.ofHom (X := liftedResidue.{t, u} π n)
    (Y := ModuleCat.of (ULift.{t} (A ⧸ powerIdeal π (n + 1)))
      (ULift.{t} (A ⧸ powerIdeal π (n + 1))))
    { toFun := fun x ↦ ULift.up (residueInjection π n x.down)
      map_add' := fun x y ↦ congrArg ULift.up ((residueInjection π n).map_add x.down y.down)
      map_smul' := by
        intro a x
        apply ULift.ext
        exact residueInjection_mul π n a.down x.down }

private def liftedQuotient (n : ℕ) :
    ModuleCat.of (ULift.{t} (A ⧸ powerIdeal π (n + 1)))
      (ULift.{t} (A ⧸ powerIdeal π (n + 1))) ⟶ liftedTarget.{t, u} π n :=
  letI : Module (ULift.{t} (A ⧸ powerIdeal π (n + 1)))
      (liftedTarget.{t, u} π n) := (liftedTarget.{t, u} π n).isModule
  ModuleCat.ofHom
    (X := ModuleCat.of (ULift.{t} (A ⧸ powerIdeal π (n + 1)))
      (ULift.{t} (A ⧸ powerIdeal π (n + 1)))) (Y := liftedTarget.{t, u} π n)
    { toFun := fun x ↦ ULift.up (powerQuotient π n x.down)
      map_add' := fun x y ↦ congrArg ULift.up ((powerQuotient π n).map_add x.down y.down)
      map_smul' := by
        intro a x
        apply ULift.ext
        exact (Ideal.Quotient.factorPow (Ideal.span {π})
          (Nat.le_succ n)).map_mul a.down x.down }

private theorem liftedSequence_zero (n : ℕ) :
    liftedInjection.{t, u} π n ≫ liftedQuotient.{t, u} π n = 0 := by
  let : Module (ULift.{t} (A ⧸ powerIdeal π (n + 1)))
      (liftedResidue.{t, u} π n) := (liftedResidue.{t, u} π n).isModule
  let : Module (ULift.{t} (A ⧸ powerIdeal π (n + 1)))
      (liftedTarget.{t, u} π n) := (liftedTarget.{t, u} π n).isModule
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ULift.ext
  exact DFunLike.congr_fun (residueSequence_zero π n) x.down

private theorem liftedSequence_shortExact [IsDomain A] (hπ : π ≠ 0) (n : ℕ) :
    (ShortComplex.mk (liftedInjection.{t, u} π n) (liftedQuotient.{t, u} π n)
      (liftedSequence_zero π n)).ShortExact := by
  let : Module (ULift.{t} (A ⧸ powerIdeal π (n + 1)))
      (liftedResidue.{t, u} π n) := (liftedResidue.{t, u} π n).isModule
  let : Module (ULift.{t} (A ⧸ powerIdeal π (n + 1)))
      (liftedTarget.{t, u} π n) := (liftedTarget.{t, u} π n).isModule
  apply ModuleCat.shortComplex_shortExact
  · intro x
    change ULift.up (powerQuotient π n x.down) = (0 : ULift.{t} (A ⧸ powerIdeal π n)) ↔ _
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := (residueSequence_exact π n x.down).1 (congrArg ULift.down hx)
      exact ⟨ULift.up y, congrArg ULift.up hy⟩
    · rintro ⟨y, rfl⟩
      apply ULift.ext
      exact DFunLike.congr_fun (residueSequence_zero π n) y.down
  · intro x y h
    apply ULift.ext
    exact residueInjection_injective π hπ n (congrArg ULift.down h)
  · intro y
    obtain ⟨x, hx⟩ := powerQuotient_surjective π n y.down
    exact ⟨ULift.up x, congrArg ULift.up hx⟩

section ConstantModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{r}] [J.WEqualsLocallyBijective CommRingCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]

private abbrev constantRing (A : Type r) [CommRing A] : Sheaf J RingCat.{r} :=
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
    ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of A))

private def constantRingUnit (A : Type r) [CommRing A] :
    (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ (constantRing J A).obj :=
  Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
    (forget₂ CommRingCat.{r} RingCat.{r})

private instance constantRingUnit_injective (A : Type r) [CommRing A] :
    Presheaf.IsLocallyInjective J (constantRingUnit J A) where
  equalizerSieve_mem x y h := Presheaf.equalizerSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))) x y h

private instance constantRingUnit_surjective (A : Type r) [CommRing A] :
    Presheaf.IsLocallySurjective J (constantRingUnit J A) where
  imageSieve_mem x := Presheaf.imageSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))) x

private def constantModulePresheaf (A : Type r) [CommRing A] :
    ModuleCat.{r} A ⥤ PresheafOfModules.{r} ((Functor.const Cᵒᵖ).obj (RingCat.of A)) where
  obj M := { obj := fun _ ↦ M, map := fun _ ↦ ModuleCat.ofHom LinearMap.id }
  map f := { app := fun _ ↦ f }

private def constantModuleFunctor (A : Type r) [CommRing A] :
    ModuleCat.{r} A ⥤ SheafOfModules.{r} (constantRing J A) :=
  constantModulePresheaf (C := C) A ⋙
    PresheafOfModules.sheafification.{r} (constantRingUnit J A)

private theorem constantModuleFunctor_exact (A : Type r) [CommRing A] :
    (constantModuleFunctor J A).Additive ∧
      PreservesFiniteLimits (constantModuleFunctor J A) ∧
      PreservesFiniteColimits (constantModuleFunctor J A) := by
  let P := constantModulePresheaf (C := C) A
  have : PreservesFiniteLimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun _ ↦ hc)⟩
  have : PreservesFiniteColimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun _ ↦ hc)⟩
  change (P ⋙ PresheafOfModules.sheafification.{r} (constantRingUnit J A)).Additive ∧
    PreservesFiniteLimits (P ⋙ PresheafOfModules.sheafification.{r} (constantRingUnit J A)) ∧
    PreservesFiniteColimits (P ⋙ PresheafOfModules.sheafification.{r} (constantRingUnit J A))
  have : PreservesFiniteLimits
      (P ⋙ PresheafOfModules.sheafification.{r} (constantRingUnit J A)) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits
      (P ⋙ PresheafOfModules.sheafification.{r} (constantRingUnit J A)) :=
    comp_preservesFiniteColimits _ _
  refine ⟨?_, inferInstance, inferInstance⟩
  apply leftExactFunctor_le_additiveFunctor _ _
  rw [leftExactFunctor_iff]
  infer_instance

private instance constantModuleFunctor_additive (A : Type r) [CommRing A] :
    (constantModuleFunctor J A).Additive := (constantModuleFunctor_exact J A).1

end ConstantModules

section ConstantCoefficientComparison

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{max u v r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})]
  [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v r}]
  (A B : CommRingCat.{max u v r}) (f : A →+* B)

private def constantRingMap : constantRing J A ⟶ constantRing J B :=
  ((constantSheaf J CommRingCat.{max u v r}) ⋙
    sheafCompose J (forget₂ CommRingCat RingCat)).map (CommRingCat.ofHom f)

private def constantCoefficient : SheafOfModules.{max u v r} (constantRing J A) :=
  (SheafOfModules.restrictScalars (constantRingMap.{u, v, r} J A B f)).obj
    (SheafOfModules.unit (constantRing J B))

private def constantCoefficientIso :
    (constantModuleFunctor J A).obj ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) ≅
      constantCoefficient.{u, v, r} J A B f := by
  letI := f.toAlgebra
  exact asIso (CategoryTheory.basisLift.{u, v, r} J A B)

private theorem constantCoefficientIso_unit (U : Cᵒᵖ) (x : B) :
    (constantCoefficientIso.{u, v, r} J A B f).hom.val.app U
      (((PresheafOfModules.sheafificationAdjunction (constantRingUnit J A)).unit.app
        ((constantModulePresheaf (C := C) A).obj
          ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)))).app U x) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U x := by
  let := f.toAlgebra
  change (CategoryTheory.basisLift.{u, v, r} J A B).val.app U _ = _
  rw [CategoryTheory.basisLift]
  let e := PresheafOfModules.sheafificationHomEquiv
    (CategoryTheory.basisRingUnit.{u, v, r} J A)
    (P := (CategoryTheory.basisConst (C := C) A).obj (ModuleCat.of A B))
    (F := CategoryTheory.basisTarget.{u, v, r} J A B)
  exact congrArg (fun k ↦ k.app U x)
    (e.apply_symm_apply (CategoryTheory.basisConstToTarget.{u, v, r} J A B))

variable (D : CommRingCat.{max u v r}) (g : A →+* D)

private def constantCoefficientMap
    (h : (ModuleCat.restrictScalars f).obj (ModuleCat.of B B) ⟶
      (ModuleCat.restrictScalars g).obj (ModuleCat.of D D)) :
    constantCoefficient.{u, v, r} J A B f ⟶ constantCoefficient.{u, v, r} J A D g :=
  (constantCoefficientIso.{u, v, r} J A B f).inv ≫ (constantModuleFunctor J A).map h ≫
    (constantCoefficientIso.{u, v, r} J A D g).hom

private theorem constantCoefficientMap_unit
    (h : (ModuleCat.restrictScalars f).obj (ModuleCat.of B B) ⟶
      (ModuleCat.restrictScalars g).obj (ModuleCat.of D D)) (U : Cᵒᵖ) (x : B) :
    (constantCoefficientMap.{u, v, r} J A B f D g h).val.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U x) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj D)).app U (h x) := by
  rw [← constantCoefficientIso_unit.{u, v, r} J A B f]
  let M := (ModuleCat.restrictScalars f).obj (ModuleCat.of B B)
  let N := (ModuleCat.restrictScalars g).obj (ModuleCat.of D D)
  let P := constantModulePresheaf (C := C) A
  let adj := PresheafOfModules.sheafificationAdjunction (constantRingUnit J A)
  have hi := congrArg (fun k ↦ k.val.app U ((adj.unit.app (P.obj M)).app U x))
    (constantCoefficientIso.{u, v, r} J A B f).hom_inv_id
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] at hi
  change (constantCoefficientIso.{u, v, r} J A D g).hom.val.app U
    (((constantModuleFunctor J A).map h).val.app U
      ((constantCoefficientIso.{u, v, r} J A B f).inv.val.app U
        ((constantCoefficientIso.{u, v, r} J A B f).hom.val.app U _))) = _
  rw [hi]
  have hn := congrArg (fun k ↦ k.app U x) (adj.unit.naturality (P.map h))
  change (adj.unit.app (P.obj N)).app U (h x) =
    ((constantModuleFunctor J A).map h).val.app U ((adj.unit.app (P.obj M)).app U x) at hn
  rw [← hn]
  exact constantCoefficientIso_unit.{u, v, r} J A D g U (h x)

end ConstantCoefficientComparison

end StrictDvrCoefficientProof

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})

private instance (priority := 4000) strictDvrSiteSmall :
    EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf.{u} X.ProEt

private instance strictDvrRingSheafify :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      CommRingCat.{max u (t + 1)} := integralCoefficientRingSheafify.{t, u} X

private instance strictDvrAbSheafify :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X

private instance strictDvrAbLocallyBijective :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} X

/-- The finite coefficient as a module over the completion.
Source: Stacks 0942 (blueprint: def-sf-strict-dvr-coefficient-sequence-data). -/
abbrev strictDvrFiniteCoefficient (n : ℕ) : scalarReductionSource l E X :=
  (scalarReductionRestriction l E X n).obj
    (SheafOfModules.unit (integralCoefficientSheaf l E X n))

/-- The canonical quotient map with its completed-ring action.
Source: Stacks 0942 (blueprint: def-sf-strict-dvr-coefficient-sequence-data). -/
def strictDvrCoefficientQuotient (n : ℕ) :
    strictDvrFiniteCoefficient l E X (n + 1) ⟶ strictDvrFiniteCoefficient l E X n where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (strictDvrFiniteCoefficient l E X (n + 1)).val.obj U)
        (Y := (strictDvrFiniteCoefficient l E X n).val.obj U)
        { toFun := (integralCoefficientSheafTransition l E X n).hom.app U
          map_add' := map_add _
          map_smul' := by
            intro c x
            change (integralCoefficientSheaf l E X (n + 1)).obj.obj U at x
            change (integralCoefficientSheafTransition l E X n).hom.app U
                ((show (integralCoefficientSheaf l E X (n + 1)).obj.obj U from
                  (limit.π (integralCoefficientSheafSystem l E X) (op (n + 1))).hom.app U c) * x) =
              (show (integralCoefficientSheaf l E X n).obj.obj U from
                (limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app U c) *
                (integralCoefficientSheafTransition l E X n).hom.app U x
            rw [map_mul]
            congr 1
            have h : (limit.π (integralCoefficientSheafSystem l E X)
                (op (n + 1))).hom.app U ≫
                (integralCoefficientSheafTransition l E X n).hom.app U =
                (limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app U := by
              have h₀ := congrArg (fun k ↦ k.hom.app U)
                (limit.w (integralCoefficientSheafSystem l E X)
                  (homOfLE (Nat.le_succ n)).op)
              simpa only [integralCoefficientSheafSystem,
                Functor.ofOpSequence_map_homOfLE_succ,
                ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using h₀
            exact ConcreteCategory.congr_hom h c }
      naturality := by
        intro U V f
        ext x
        exact ConcreteCategory.congr_hom
          ((integralCoefficientSheafTransition l E X n).hom.naturality f) x }

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits

open StrictDvrCoefficientProof

private abbrev finiteRing (n : ℕ) : CommRingCat.{max u (t + 1)} :=
  CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))

private abbrev completionProjection (n : ℕ) :
    completedIntegralCoefficientSheafUnrestricted l E X ⟶ integralCoefficientSheaf l E X n := by
  unfold completedIntegralCoefficientSheafUnrestricted
  exact limit.π (integralCoefficientSheafSystem l E X) (op n)

private def finitePresentationIso (N k : ℕ)
    (f : finiteRing.{t, u} l E N →+* finiteRing.{t, u} l E k)
    (hf : completionProjection l E X N ≫
      constantRingMap.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology X)
        (finiteRing.{t, u} l E N) (finiteRing.{t, u} l E k) f = completionProjection l E X k) :
    (scalarReductionRestriction l E X N).obj
      ((constantModuleFunctor.{t + 1, t, max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt.topology X)
        (finiteRing.{t, u} l E N)).obj
          ((ModuleCat.restrictScalars f).obj (ModuleCat.of (finiteRing.{t, u} l E k)
            (finiteRing.{t, u} l E k)))) ≅
      strictDvrFiniteCoefficient l E X k :=
  (scalarReductionRestriction l E X N).mapIso
    (constantCoefficientIso.{t + 1, t, u}
      (AlgebraicGeometry.Scheme.ProEt.topology X) (finiteRing.{t, u} l E N) (finiteRing.{t, u} l
        E k) f) ≪≫
    (SheafOfModules.restrictionComp (completionProjection l E X N)
      (constantRingMap.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology X)
        (finiteRing.{t, u} l E N) (finiteRing.{t, u} l E k) f)
      (completionProjection l E X k) hf).app (SheafOfModules.unit (integralCoefficientSheaf l E X
        k))

private theorem finitePresentationIso_unit (N k : ℕ)
    (f : finiteRing.{t, u} l E N →+* finiteRing.{t, u} l E k)
    (hf : completionProjection l E X N ≫
      constantRingMap.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology X)
        (finiteRing.{t, u} l E N) (finiteRing.{t, u} l E k) f = completionProjection l E X k)
    (U : X.ProEtᵒᵖ) (x : finiteRing.{t, u} l E k) :
    (finitePresentationIso l E X N k f hf).hom.val.app U
      (((PresheafOfModules.sheafificationAdjunction.{max u (t + 1), t, max u (t + 1), t + 1}
        (constantRingUnit.{t + 1, t, max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt.topology X)
          (finiteRing.{t, u} l E N))).unit.app
          ((constantModulePresheaf.{t + 1, t, max u (t + 1)} (C := X.ProEt) (finiteRing.{t, u} l
            E N)).obj
            ((ModuleCat.restrictScalars f).obj
              (ModuleCat.of (finiteRing.{t, u} l E k) (finiteRing.{t, u} l E k))))).app U x) =
      (toSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (finiteRing.{t, u} l E k))).app U x := by
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      CommRingCat.{max u (t + 1)} := integralCoefficientRingSheafify.{t, u} X
  exact constantCoefficientIso_unit.{t + 1, t, u}
    (AlgebraicGeometry.Scheme.ProEt.topology X) (finiteRing.{t, u} l E N) (finiteRing.{t, u} l E
      k) f U x

private def finiteQuotient (N k : ℕ) (h : k ≤ N) :
    finiteRing.{t, u} l E N →+* finiteRing.{t, u} l E k :=
  liftRingHom.{t + 1, u} (Ideal.Quotient.factorPow
    (Ideal.span {Padic.coefficientExtensionUniformizer l E}) (Nat.add_le_add_right h 1))

private theorem finiteQuotient_projection (N k : ℕ) (h : k ≤ N) :
    completionProjection l E X N ≫
      constantRingMap.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology X)
        (finiteRing.{t, u} l E N) (finiteRing.{t, u} l E k) (finiteQuotient.{t, u} l E N k h) =
      completionProjection l E X k := by
  rw [show constantRingMap.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology X)
      (finiteRing.{t, u} l E N) (finiteRing.{t, u} l E k) (finiteQuotient.{t, u} l E N k h) =
        (integralCoefficientSheafSystem l E X).map (homOfLE h).op from
    (AlgebraicGeometry.ProEtale.coefficientTower_map l E X k N h).symm]
  simpa only [completionProjection, completedIntegralCoefficientSheafUnrestricted, id_eq] using
    (limit.w (integralCoefficientSheafSystem l E X) (homOfLE h).op)

/-- Multiplication by the indicated uniformizer power identifies the residue sheaf with
 the kernel of the next quotient, in modules over the completion.

Source: Stacks Project, Tag 0942, proof of lemma-bounded (1), and Modules on Sites
Tags 093J, 03CY, 03DA and 03DB.
(blueprint: lem-sf-strict-dvr-coefficient-sequence)

Proof: In the valuation ring R, put A_m = R/(π^m). Multiplication by π^(n+1)
induces A_1 → A_(n+2): changing a representative by πs changes its image by
π^(n+2)s. Cancellation of the nonzero π^(n+1) in the domain R proves injectivity.
The quotient A_(n+2) → A_(n+1) is surjective and its kernel consists precisely of
classes of π^(n+1)r. The injection is linear over A_(n+2), with the source action
through A_1, as is checked by lifting the scalar and the section to R. Lift the
rings and maps by ULift and apply exact constant module realization over A_(n+2).
For its universe convention, work first on a small skeleton in the coefficient
universe and transport module sheaves back along the site equivalence; alternatively
construct the constant module presheaf sectionwise and use exact module sheafification.
The constant-module sheafification unit identifies these sheaves with the restrictions
of the constant quotient ring sheaves; the injection has the asserted formula on
constant sections. Restrict scalars along the completion projection to A_(n+2).
The limit projection equations identify the outer actions with their recorded
completion actions. Restriction preserves exactness, since it leaves the underlying
abelian sheaves unchanged. The resulting quotient is the explicitly constructed
strictDvrCoefficientQuotient, and the zero equation and short exactness follow. -/
theorem strictDvrCoefficientSequence :
    ∃ (a : ∀ n : ℕ, strictDvrFiniteCoefficient l E X 0 ⟶
        strictDvrFiniteCoefficient l E X (n + 1)),
      (∀ (n : ℕ) (U : X.ProEtᵒᵖ) (r : Padic.coefficientExtensionIntegers l E),
        (a n).val.app U
          ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj
              (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E 1))))).app U
                (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1) r))) =
          (toSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj
              (CommRingCat.of
                (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1 + 1)))))).app U
                  (ULift.up (Ideal.Quotient.mk
                    (Padic.coefficientExtensionIdeal l E (n + 1 + 1))
                    (Padic.coefficientExtensionUniformizer l E ^ (n + 1) * r)))) ∧
      ∀ n : ℕ, ∃ hz : a n ≫ strictDvrCoefficientQuotient l E X n = 0,
        (ShortComplex.mk (a n) (strictDvrCoefficientQuotient l E X n) hz).ShortExact := by
  classical
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      CommRingCat.{max u (t + 1)} := integralCoefficientRingSheafify.{t, u} X
  let J := AlgebraicGeometry.Scheme.ProEt.topology X
  let π := Padic.coefficientExtensionUniformizer l E
  let F (n : ℕ) := constantModuleFunctor.{t + 1, t, max u (t + 1)} J (finiteRing.{t, u} l E (n +
    1)) ⋙
    scalarReductionRestriction l E X (n + 1)
  have (n : ℕ) : PreservesFiniteLimits (F n) := by
    have : PreservesFiniteLimits
        (constantModuleFunctor.{t + 1, t, max u (t + 1)} J (finiteRing.{t, u} l E (n + 1))) :=
      (constantModuleFunctor_exact J (finiteRing.{t, u} l E (n + 1))).2.1
    have : PreservesFiniteLimits (scalarReductionRestriction l E X (n + 1)) :=
      scalarReductionRestrictionLimits l E X (n + 1)
    exact comp_preservesFiniteLimits _ _
  have (n : ℕ) : PreservesFiniteColimits (F n) := by
    have : PreservesFiniteColimits
        (constantModuleFunctor.{t + 1, t, max u (t + 1)} J (finiteRing.{t, u} l E (n + 1))) :=
      (constantModuleFunctor_exact J (finiteRing.{t, u} l E (n + 1))).2.2
    have : PreservesFiniteColimits (scalarReductionRestriction l E X (n + 1)) :=
      scalarReductionRestrictionColimits l E X (n + 1)
    exact comp_preservesFiniteColimits _ _
  let S (n : ℕ) := ShortComplex.mk (liftedInjection.{t + 1, u} π (n + 1))
    (liftedQuotient.{t + 1, u} π (n + 1)) (liftedSequence_zero π (n + 1))
  let f₀ (n : ℕ) := finiteQuotient.{t, u} l E (n + 1) 0 (Nat.zero_le _)
  let f₂ (n : ℕ) := finiteQuotient.{t, u} l E (n + 1) n (Nat.le_succ n)
  have hmid (n : ℕ) : completionProjection l E X (n + 1) ≫
      constantRingMap.{t + 1, t, u} J (finiteRing.{t, u} l E (n + 1)) (finiteRing.{t, u} l E (n +
        1))
        (RingHom.id _) = completionProjection l E X (n + 1) := by
    change completionProjection l E X (n + 1) ≫
      ((constantSheaf J CommRingCat.{max u (t + 1)}) ⋙
        sheafCompose J (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (𝟙 (finiteRing.{t, u} l E (n + 1))) = _
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  let e₀ (n : ℕ) : (F n).obj (S n).X₁ ≅ strictDvrFiniteCoefficient l E X 0 :=
    finitePresentationIso l E X (n + 1) 0 (f₀ n)
      (finiteQuotient_projection l E X (n + 1) 0 (Nat.zero_le _))
  let e₁ (n : ℕ) : (F n).obj (S n).X₂ ≅ strictDvrFiniteCoefficient l E X (n + 1) :=
    finitePresentationIso l E X (n + 1) (n + 1) (RingHom.id _) (hmid n)
  let e₂ (n : ℕ) : (F n).obj (S n).X₃ ≅ strictDvrFiniteCoefficient l E X n :=
    finitePresentationIso l E X (n + 1) n (f₂ n)
      (finiteQuotient_projection l E X (n + 1) n (Nat.le_succ n))
  let a (n : ℕ) := (e₀ n).inv ≫ (F n).map (S n).f ≫ (e₁ n).hom
  have hb (n : ℕ) : (e₁ n).inv ≫ (F n).map (S n).g ≫ (e₂ n).hom =
      strictDvrCoefficientQuotient l E X n := by
    apply (cancel_epi (e₁ n).hom).1
    simp only [Iso.hom_inv_id_assoc]
    apply (SheafOfModules.toSheaf (completedIntegralCoefficientSheafUnrestricted l E
      X)).map_injective
    apply ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{max u (t + 1)}).homEquiv _
      _).injective
    ext U x
    let P := constantModulePresheaf.{t + 1, t, max u (t + 1)} (C := X.ProEt) (finiteRing.{t, u} l
      E (n + 1))
    let adj := PresheafOfModules.sheafificationAdjunction.{max u (t + 1), t, max u (t + 1), t + 1}
      (constantRingUnit.{t + 1, t, max u (t + 1)} J (finiteRing.{t, u} l E (n + 1)))
    change (e₂ n).hom.val.app U
      (((F n).map (S n).g).val.app U ((adj.unit.app (P.obj (S n).X₂)).app U x)) =
      (strictDvrCoefficientQuotient l E X n).val.app U
        ((e₁ n).hom.val.app U ((adj.unit.app (P.obj (S n).X₂)).app U x))
    have hn := congrArg (fun k ↦ k.app U x) (adj.unit.naturality (P.map (S n).g))
    change (adj.unit.app (P.obj (S n).X₃)).app U ((S n).g x) =
      (((F n).map (S n).g).val.app U ((adj.unit.app (P.obj (S n).X₂)).app U x)) at hn
    rw [← hn]
    erw [finitePresentationIso_unit, finitePresentationIso_unit]
    have hx : (S n).g x = f₂ n x := by
      rcases x with ⟨x⟩
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    rw [hx]
    exact congrArg (fun k ↦ k.app U x)
      (toSheafify_naturality J ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom (f₂ n))))
  have hz (n : ℕ) : a n ≫ strictDvrCoefficientQuotient l E X n = 0 := by
    rw [← hb]
    dsimp only [a]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc ((F n).map (S n).f) ((F n).map (S n).g) ((e₂ n).hom),
      ← Functor.map_comp, (S n).zero, Functor.map_zero, zero_comp, comp_zero]
  refine ⟨a, ?_, fun n ↦ ⟨hz n, ?_⟩⟩
  · intro n U r
    change (constantCoefficientMap.{t + 1, t, u} J (finiteRing.{t, u} l E (n + 1))
      (finiteRing.{t, u} l E 0) (f₀ n)
      (finiteRing.{t, u} l E (n + 1)) (RingHom.id _) (S n).f).val.app U _ = _
    rw [constantCoefficientMap_unit]
    rfl
  · have hS : (S n).ShortExact := liftedSequence_shortExact.{t + 1, u} π
      (AlgebraicGeometry.ProEtale.uniformizer_ne_zero l E) (n + 1)
    apply ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (e₀ n) (e₁ n) (e₂ n) ?_ ?_)
      (hS.map_of_exact (F n))
    · simp [a]
    · change (e₁ n).hom ≫ strictDvrCoefficientQuotient l E X n =
        (F n).map (S n).g ≫ (e₂ n).hom
      rw [← hb]
      simp

end WeilConjectures
