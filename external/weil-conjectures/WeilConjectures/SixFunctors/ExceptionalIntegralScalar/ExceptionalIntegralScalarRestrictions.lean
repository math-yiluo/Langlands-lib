/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralLeftScalarData
import all WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalCompletedChangeInjective
import WeilConjectures.SixFunctors.PurCompactSupport.ExceptionalCanonicalScalarExact
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.FiniteScalarPreservation
import WeilConjectures.SmoothPurity.Finite.FiniteTorIntegralCompletedScalarExtension
import all WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import all WeilConjectures.SmoothPurity.Pur.PurAdicScalarExtensionTorBound

/-! # Normalized scalar restrictions, independently of exceptional operations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
attribute [local irreducible] HasDerivedCategory.standard
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

-- Coefficient presentations and full-subcategory instances need this reduction budget.
/-- The scalar-only part of the left comparison construction. It contains neither
an exceptional operation nor a proper/open comparison.
Source: Zheng, Construction 4.1 and Proposition 5.24.
(blueprint: def-sf-integral-scalar-restrictions). -/
structure ScalarRestrictions (T : Scheme.{u}) where
  scalar {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) : Scalar.{u} l Ω a T
  scalarShift {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) : (scalar a ha).realization.hom.CommShift ℤ
  finiteScalar_eq {s : RingStage.{u} l} (E : FieldStage.{u} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a) :
    (scalar (s := s) (t := .finite E n) a ha).functor ⋙
        RingStage.inclusion.{u} l Ω T (RingStage.finite E n) =
      RingStage.inclusion.{u} l Ω T s ⋙
        pbcDerivedExtend (a.map T)
  finiteScalar_normalized {s : RingStage.{u} l} (E : FieldStage.{u} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a) :
    (scalar (s := s) (t := .finite E n) a ha).realization =
      eqToIso (finiteScalar_eq (s := s) E n a ha)
  integralScalar_eq (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    (scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i)).functor ⋙
        RingStage.inclusion.{u} l Ω T (RingStage.integral L) =
      RingStage.inclusion.{u} l Ω T (RingStage.integral E) ⋙
        integralScalarExtensionOfUniverses l E.carrier L.carrier i T
  integralScalar_normalized (E L : FieldStage.{u} l)
      (i : E.carrier →ₐ[Padic l] L.carrier)
      (K : C.{u} l Ω T (.integral E)) :
    HEq ((scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i)).realization.inv.app K)
      ((completedScalarComparison l E.carrier L.carrier i T).app K.obj)
  tor_interval (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (K : C.{u} l Ω T (.integral E)) (a b : ℤ)
      (h : ∀ n : ℕ, HasProEtaleTorAmplitude T
        (Padic.coefficientExtensionRing l E.carrier (n + 1))
        ((scalarReductionDerivedExtension l E.carrier T n).obj K.obj) a b) :
    ∀ n : ℕ, HasProEtaleTorAmplitude T
      (Padic.coefficientExtensionRing l L.carrier (n + 1))
      ((scalarReductionDerivedExtension l L.carrier T n).obj
        ((scalar (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i)).functor.obj K).obj) a b

-- Coefficient presentations and full-subcategory instances need this reduction budget.
private def IntegralOrigin {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)) : Prop :=
  match s, t with
  | _, .finite _ _ => True
  | .finite _ _, .integral _ => False
  | .integral E, .integral L =>
    ∃ i : E.carrier →ₐ[Padic l] L.carrier, ∀ T : Scheme.{u},
      a.map T = completedCoefficientMap l E.carrier L.carrier i T

-- Coefficient presentations and full-subcategory instances need this reduction budget.
private theorem allowed_integralOrigin {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (ha : Allowed l a) : IntegralOrigin l a := by
  induction ha with
  | quotient => trivial
  | ramified => trivial
  | reduction => trivial
  | integral E L i => exact ⟨i, fun _ ↦ rfl⟩
  | identity s a h =>
    cases s with
    | finite => trivial
    | integral E =>
      exact ⟨AlgHom.id (Padic l) E.carrier, fun T ↦
        (h T).trans (PurCompactSupport.completedMap_identity l E.carrier T).symm⟩
  | @comp s t r a b d h ha hb iha ihb =>
    cases r with
    | finite => trivial
    | integral R =>
      cases t with
      | finite => exact ihb.elim
      | integral T =>
        cases s with
        | finite => exact iha.elim
        | integral S =>
          obtain ⟨i, hi⟩ := iha
          obtain ⟨j, hj⟩ := ihb
          refine ⟨j.comp i, fun W ↦ ?_⟩
          rw [← h W, hi W, hj W]
          exact PurCompactSupport.completedMap_composition
            l S.carrier T.carrier i R.carrier j W

-- Coefficient presentations and full-subcategory instances need this reduction budget.
private def stageProperty (T : Scheme.{u}) (s : RingStage.{u} l) :
    ObjectProperty (DerivedCategory (pbcModules T ((s.coefficients l).ring T))) :=
  match s with
  | .finite E n => finiteTorConstructible l E.carrier n n.pos T
  | .integral E => finiteTorConstructibleIntegral l E.carrier T

-- Coefficient presentations and full-subcategory instances need this reduction budget.
private theorem stageProperty_of_iso (T : Scheme.{u}) (s : RingStage.{u} l)
    {K L : DerivedCategory (pbcModules T ((s.coefficients l).ring T))}
    (e : K ≅ L) (h : stageProperty l T s K) : stageProperty l T s L := by
  cases s with
  | finite E n =>
    have hc : (finiteTorConstructible l E.carrier n n.pos T).IsClosedUnderIsomorphisms :=
      (finite_ctf_isTriangulated l E.carrier n n.pos T).1
    exact (finiteTorConstructible l E.carrier n n.pos T).prop_of_iso e h
  | integral E =>
    refine ⟨(sfIntegralConstructible l E.carrier T).prop_of_iso e h.1, ?_⟩
    obtain ⟨a, b, hab, hbounds⟩ := h.2
    refine ⟨a, b, hab, fun n ↦ ⟨(hbounds n).1, ?_⟩⟩
    intro N P he f hf hP M k hk
    obtain ⟨eN⟩ := he
    exact (hbounds n).2 N P
      ⟨eN ≪≫ (scalarReductionDerivedExtension l E.carrier T n).mapIso e.symm⟩
      f hf hP M k hk

-- Coefficient presentations and full-subcategory instances need this reduction budget.
private theorem finiteMap_preserves (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    (E L : FieldStage.{u} l) (m n : ℕ+)
    (a : Padic.coefficientExtensionRing l E.carrier m →+*
      Padic.coefficientExtensionRing l L.carrier n)
    (K : proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E.carrier m))
    (hK : finiteTorConstructible l E.carrier m m.pos T K) :
    finiteTorConstructible l L.carrier n n.pos T
      ((pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)).obj K) := by
  rcases m with ⟨m, hm⟩
  rcases n with ⟨n, hn⟩
  cases m with
  | zero => omega
  | succ m =>
    cases n with
    | zero => omega
    | succ n =>
      exact ExceptionalFiniteScalar.finiteScalar_preserves D l hl E.carrier L.carrier
        m n a T ⟨K, hK⟩

-- Coefficient presentations and full-subcategory instances need this reduction budget.
private theorem allowed_preserves (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (ha : Allowed l a) :
    ∀ K, stageProperty l T s K →
      stageProperty l T t ((pbcDerivedExtend (a.map T)).obj K) := by
  induction ha with
  | quotient E m n h =>
    intro K hK
    change finiteTorConstructible _ _ _ _ _ _
    rw [show (PurCompactSupport.finiteQuotientChange l E.carrier m n m.pos n.pos h).map T =
      proEtaleConstantRingMap (T := T) (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right h)) from
      PurCompactSupport.finiteQuotient_eq_map l E.carrier m n m.pos n.pos h T]
    exact finiteMap_preserves l D hl T E E m n _ K hK
  | ramified E L i e he n =>
    intro K hK
    exact finiteMap_preserves l D hl T E L n ⟨e * n, Nat.mul_pos e.pos n.pos⟩
      (PurCompactSupport.ramifiedMap l E.carrier L.carrier i e he n) K hK
  | reduction E n =>
    intro K hK
    rcases n with ⟨n, hn⟩
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨hcon, a, b, hab, htor⟩ := hK
      obtain ⟨hc, c, d, hcd, hconstructible⟩ := hcon
      have hred : finiteTorConstructible l E.carrier (n + 1) hn T
          ((scalarReductionDerivedExtension l E.carrier T n).obj K) :=
        ⟨(hconstructible n).1, ⟨a, b, htor n⟩⟩
      exact stageProperty_of_iso l T (.finite E ⟨n + 1, hn⟩)
        ((PurCompactSupport.finiteReductionIso l E.carrier T n).app K).symm hred
  | integral E L i =>
    intro K hK
    exact finiteTorIntegralCompletedScalarExtension D.p l hl E.carrier L.carrier i T K hK
  | identity s a h =>
    intro K hK
    exact stageProperty_of_iso l T s
      (((eqToIso (congrArg pbcDerivedExtend (h T))) ≪≫
        PurCompactSupport.tensorIdentity ((s.coefficients l).ring T)).app K).symm hK
  | @comp s t r a b d h ha hb iha ihb =>
    intro K hK
    exact stageProperty_of_iso l T r
      ((PurCompactSupport.tensorComposition (a.map T) (b.map T) (d.map T) (h T)).app K)
      (ihb _ (iha K hK))

private theorem stageProperty_tri (T : Scheme.{u}) (s : RingStage.{u} l) :
    (stageProperty l T s).IsTriangulated := by
  cases s with
  | finite E n => exact (finite_ctf_isTriangulated l E.carrier n n.pos T).2.1
  | integral E => exact ConstructibleExceptionalCoefficients.integralTriangulated l E T

-- Coefficient presentations and full-subcategory instances need this reduction budget.
private def ambientScalar (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (ha : Allowed l a) : Scalar.{u} l Ω a T := by
  let P := stageProperty l T s
  let Q := stageProperty l T t
  let h := allowed_preserves l D hl T a ha
  have := PurCompactSupport.canonicalScalarExact (a.map T)
  have : P.IsTriangulated := stageProperty_tri l T s
  have : Q.IsTriangulated := stageProperty_tri l T t
  cases s <;> cases t
  all_goals
    let F := P.liftFullSubcategory Q (pbcDerivedExtend (a.map T)) h
    exact {
      functor := F
      realization := P.liftFullSubcategoryCompιIso Q (pbcDerivedExtend (a.map T)) h
      commShift := inferInstance
      additive := inferInstance
      exact := ObjectProperty.isTriangulated_liftFullSubcategory P Q _ h }

-- Coefficient presentations and full-subcategory instances need this reduction budget.
-- Coefficient presentations and full-subcategory instances need this reduction budget.
-- Coefficient presentations and full-subcategory instances need this reduction budget.
private theorem ambientScalar_shift (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (ha : Allowed l a) :
    (ambientScalar l Ω D hl T a ha).realization.hom.CommShift ℤ := by
  have : (stageProperty l T s).IsTriangulated := stageProperty_tri l T s
  have : (stageProperty l T t).IsTriangulated := stageProperty_tri l T t
  cases s <;> cases t <;> dsimp only [ambientScalar] <;> infer_instance

-- Coefficient presentations and full-subcategory instances need this reduction budget.
private theorem completedChi_isIso (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (T : Scheme.{u}) (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (K : finiteTorConstructibleIntegralCategory l E.carrier T) :
    IsIso ((completedScalarComparison l E.carrier L.carrier i T).app K.obj) := by
  have hc : IsDerivedCompleteUnrestricted l E.carrier T K.obj := by
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    have : Fact p.Prime := ⟨hprime⟩
    let D₀ : FiniteFieldDatum.{0} :=
      { p := p
        a := 1
        q := p
        prime := hprime
        exponent_pos := le_refl 1
        cardinality_eq := (pow_one p).symm
        k₀ := ZMod p
        card_base := by simp [Nat.card_eq_fintype_card]
        k := AlgebraicClosure (ZMod p) }
    have hl₀ : l ≠ D₀.p := by change l ≠ p; omega
    exact ⟨D₀, hl₀, (sfDerivedComplete_iff_legacy l E.carrier T D₀ hl₀ K.obj).mp
      K.property.1.1⟩
  exact ((finiteFreeCompletedScalarComparison l E.carrier L.carrier i T).2.1 K.obj hc).1

private structure ShiftedScalar (T : Scheme.{u}) {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)) where
  scalar : Scalar.{u} l Ω a T
  shift : scalar.realization.hom.CommShift ℤ

-- Coefficient presentations and full-subcategory instances need this reduction budget.
private def completedShifted (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : Scheme.{u}) (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    ShiftedScalar l Ω T (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i) := by
  let P := finiteTorConstructibleIntegral l E.carrier T
  let Q := finiteTorConstructibleIntegral l L.carrier T
  have hchi (K : P.FullSubcategory) :
      IsIso ((completedScalarComparison l E.carrier L.carrier i T).app K.obj) :=
    completedChi_isIso l D hl T E L i K
  let preserve : ∀ K, P K → Q ((integralScalarExtensionOfUniverses
      l E.carrier L.carrier i T).obj K) := by
    intro K hK
    have hi := hchi ⟨K, hK⟩
    exact stageProperty_of_iso l T (.integral L)
      (asIso ((completedScalarComparison l E.carrier L.carrier i T).app K))
      (finiteTorIntegralCompletedScalarExtension D.p l hl E.carrier L.carrier i T K hK)
  let F := P.liftFullSubcategory Q
    (integralScalarExtensionOfUniverses l E.carrier L.carrier i T) preserve
  have : IsIso (Functor.whiskerLeft P.ι
      (completedScalarComparison l E.carrier L.carrier i T)) := by
    exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun K ↦ hchi K)
  let realization : F ⋙ Q.ι ≅ P.ι ⋙
      pbcDerivedExtend (completedCoefficientMap l E.carrier L.carrier i T) :=
    (P.liftFullSubcategoryCompιIso Q _ preserve) ≪≫
      (asIso (Functor.whiskerLeft P.ι
        (completedScalarComparison l E.carrier L.carrier i T))).symm
  let shift : F.CommShift ℤ := Functor.CommShift.ofComp realization ℤ
  letI := shift
  have hshift : realization.hom.CommShift ℤ := Functor.CommShift.ofComp_compatibility _ _
  have := PurCompactSupport.canonicalScalarExact
    (completedCoefficientMap l E.carrier L.carrier i T)
  have hexact : F.IsTriangulated :=
    (Functor.isTriangulated_iff_comp_right realization).mpr inferInstance
  exact ⟨{
    functor := F
    realization := realization
    commShift := shift
    additive := inferInstance
    exact := hexact }, hshift⟩

-- Coefficient presentations and full-subcategory instances need this reduction budget.
private theorem change_eq_of_map {R S : PurCompactSupport.Coefficients.{u}}
    (a b : PurCompactSupport.Change R S) (h : ∀ T, a.map T = b.map T) : a = b := by
  cases a
  cases b
  congr
  funext T
  exact h T

private theorem scalarTransport
    {A B : Type*} (f : A → B) (hf : Function.Injective f)
    (V : B → Type*) (G : ∀ a, V (f a)) (a b : A) (h : f a = f b) :
    (h ▸ G a) = G b := by
  have hab : a = b := hf h
  subst b
  cases h
  rfl

private def scalarDescend {A B : Type*} (f : A → B)
    (V : B → Type*) (G : ∀ a, V (f a)) (b : B) (h : ∃ a, b = f a) : V b :=
  h.choose_spec.symm ▸ G h.choose

private theorem scalarDescend_at {A B : Type*} (f : A → B) (hf : Function.Injective f)
    (V : B → Type*) (G : ∀ a, V (f a)) (a : A) (h : ∃ a', f a = f a') :
    scalarDescend f V G (f a) h = G a :=
  scalarTransport f hf V G h.choose a h.choose_spec.symm

private theorem scalarDescend_predicate_at {A B : Type*} (f : A → B)
    (hf : Function.Injective f) (V : B → Type*) (G : ∀ a, V (f a))
    (a : A) (h : ∃ a', f a = f a') (P : V (f a) → Prop) (hP : P (G a)) :
    P (scalarDescend f V G (f a) h) := by
  rw [scalarDescend_at f hf V G a h]
  exact hP

private def scalarBundle (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (ha : Allowed l a) : ShiftedScalar l Ω T a := by
  classical
  cases t with
  | finite E n =>
    exact ⟨ambientScalar l Ω D hl T a ha, ambientScalar_shift l Ω D hl T a ha⟩
  | integral L =>
    cases s with
    | finite E n => exact False.elim (allowed_integralOrigin l a ha)
    | integral E =>
      let hi := allowed_integralOrigin l a ha
      exact scalarDescend (PurCompactSupport.completedChange l E.carrier L.carrier)
        (fun b ↦ ShiftedScalar l Ω T (s := .integral E) (t := .integral L) b)
        (completedShifted l Ω D hl T E L) a
        ⟨hi.choose, change_eq_of_map _ _ hi.choose_spec⟩

private structure CompletedScalarFacts (T : Scheme.{u})
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (S : ShiftedScalar l Ω T (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i)) : Prop where
  functor_eq : S.scalar.functor ⋙ RingStage.inclusion l Ω T (.integral L) =
    RingStage.inclusion l Ω T (.integral E) ⋙
      integralScalarExtensionOfUniverses l E.carrier L.carrier i T
  normalized (K : C.{u} l Ω T (.integral E)) :
    HEq (S.scalar.realization.inv.app K)
      ((completedScalarComparison l E.carrier L.carrier i T).app K.obj)
  tor_interval (K : C.{u} l Ω T (.integral E)) (a b : ℤ)
      (h : ∀ n : ℕ, HasProEtaleTorAmplitude T
        (Padic.coefficientExtensionRing l E.carrier (n + 1))
        ((scalarReductionDerivedExtension l E.carrier T n).obj K.obj) a b) :
    ∀ n : ℕ, HasProEtaleTorAmplitude T
      (Padic.coefficientExtensionRing l L.carrier (n + 1))
      ((scalarReductionDerivedExtension l L.carrier T n).obj
        (S.scalar.functor.obj K).obj) a b

-- Check the three concrete properties before transporting the scalar bundle.
private theorem completedShifted_facts (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : Scheme.{u}) (E L : FieldStage.{u} l)
    (i : E.carrier →ₐ[Padic l] L.carrier) :
    CompletedScalarFacts l Ω T E L i (completedShifted l Ω D hl T E L i) := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · intro K
    apply heq_of_eq
    change (completedScalarComparison l E.carrier L.carrier i T).app K.obj ≫ 𝟙 _ =
      (completedScalarComparison l E.carrier L.carrier i T).app K.obj
    exact Category.comp_id _
  · intro K a b h n
    have hchi := completedChi_isIso l D hl T E L i K
    obtain ⟨e⟩ := WeilConjectures.completedScalarReductionComparison
      l E.carrier L.carrier i T n
    have ht := AlgebraicGeometry.ProEtale.scalarExtension_tor
      (integralScalarQuotientMap l E.carrier L.carrier i n) T _ a b (h n)
    let ec := (scalarReductionDerivedExtension l L.carrier T n).mapIso
      (asIso ((completedScalarComparison l E.carrier L.carrier i T).app K.obj))
    refine ⟨ht.1, ?_⟩
    intro N P hN f hf hP M k hk
    obtain ⟨eN⟩ := hN
    exact ht.2 N P ⟨eN ≪≫ ec.symm ≪≫ e.app K.obj⟩ f hf hP M k hk

-- Transport only the required proposition across the uniquely determined embedding.
private theorem scalarBundle_integral_facts (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    CompletedScalarFacts l Ω T E L i
      (scalarBundle l Ω D hl T (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i)) := by
  dsimp only [scalarBundle]
  exact scalarDescend_predicate_at
    (PurCompactSupport.completedChange l E.carrier L.carrier)
    (completedChange_injective l E L)
    (fun b ↦ ShiftedScalar l Ω T (s := .integral E) (t := .integral L) b)
    (completedShifted l Ω D hl T E L) i ⟨i, rfl⟩
    (CompletedScalarFacts l Ω T E L i) (completedShifted_facts l Ω D hl T E L i)

-- Keep each record field behind its own checked interface.
-- Keep each record field behind its own checked interface.
-- Keep each record field behind its own checked interface.
-- Keep each record field behind its own checked interface.
-- Keep each record field behind its own checked interface.
-- Keep each record field behind its own checked interface.
private def freezeValue {A : Type*} (a : A) : A :=
  Classical.choose (show ∃ b : A, b = a from ⟨a, rfl⟩)

private theorem freezeValue_eq {A : Type*} (a : A) : freezeValue a = a :=
  Classical.choose_spec (show ∃ b : A, b = a from ⟨a, rfl⟩)

private theorem freezeValue_property {A : Type*} (a : A) (P : A → Prop)
    (h : P a) : P (freezeValue a) := by
  rw [freezeValue_eq]
  exact h

private structure FiniteScalarFacts (T : Scheme.{u}) {s : RingStage.{u} l}
    (E : FieldStage.{u} l) (n : ℕ+)
    (a : PurCompactSupport.Change (s.coefficients l)
      ((RingStage.finite E n).coefficients l))
    (S : ShiftedScalar l Ω T (s := s) (t := .finite E n) a) : Prop where
  functor_eq : S.scalar.functor ⋙ RingStage.inclusion l Ω T (.finite E n) =
    RingStage.inclusion l Ω T s ⋙ pbcDerivedExtend (a.map T)
  normalized : S.scalar.realization = eqToIso functor_eq

-- The finite restriction reduces to the literal lift at either source stage.
private theorem scalarBundle_finite_facts (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    {s : RingStage.{u} l} (E : FieldStage.{u} l) (n : ℕ+)
    (a : PurCompactSupport.Change (s.coefficients l)
      ((RingStage.finite E n).coefficients l))
    (ha : Allowed l (s := s) (t := .finite E n) a) :
    FiniteScalarFacts l Ω T E n a
      (scalarBundle l Ω D hl T (s := s) (t := .finite E n) a ha) := by
  cases s <;> exact ⟨rfl, rfl⟩

private def frozenBundle (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (ha : Allowed l a) : ShiftedScalar l Ω T a :=
  freezeValue (scalarBundle l Ω D hl T a ha)

-- Transfer the dependent finite equality and its normalization together.
private theorem frozenBundle_finite_facts (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    {s : RingStage.{u} l} (E : FieldStage.{u} l) (n : ℕ+)
    (a : PurCompactSupport.Change (s.coefficients l)
      ((RingStage.finite E n).coefficients l))
    (ha : Allowed l (s := s) (t := .finite E n) a) :
    FiniteScalarFacts l Ω T E n a
      (frozenBundle l Ω D hl T (s := s) (t := .finite E n) a ha) :=
  freezeValue_property
    (scalarBundle l Ω D hl T (s := s) (t := .finite E n) a ha)
    (FiniteScalarFacts l Ω T E n a) (scalarBundle_finite_facts l Ω D hl T E n a ha)

-- The wrapper is equal to the constructed bundle, including all completed data.
private theorem frozenBundle_integral_facts (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    CompletedScalarFacts l Ω T E L i
      (frozenBundle l Ω D hl T (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i)) :=
  freezeValue_property
    (scalarBundle l Ω D hl T (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i) (Allowed.integral E L i))
    (CompletedScalarFacts l Ω T E L i) (scalarBundle_integral_facts l Ω D hl T E L i)

-- Assemble the dependent record while its data family is abstract.
private theorem assembleScalarRestrictions (T : Scheme.{u})
    (bundle : ∀ {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (_ha : Allowed l a), ShiftedScalar l Ω T a)
    (finiteScalar_eq : ∀
      {s : RingStage.{u} l} (E : FieldStage.{u} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
      ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a),
      (bundle (s := s) (t := .finite E n) a ha).scalar.functor ⋙
      RingStage.inclusion.{u} l Ω T (RingStage.finite E n) =
      RingStage.inclusion.{u} l Ω T s ⋙
      pbcDerivedExtend (a.map T))
    (finiteScalar_normalized : ∀
      {s : RingStage.{u} l} (E : FieldStage.{u} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
      ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a),
      (bundle (s := s) (t := .finite E n) a ha).scalar.realization =
      eqToIso (finiteScalar_eq (s := s) E n a ha))
    (integralScalar_eq : ∀
      (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier),
      (bundle (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i)
      (Allowed.integral E L i)).scalar.functor ⋙
      RingStage.inclusion.{u} l Ω T (RingStage.integral L) =
      RingStage.inclusion.{u} l Ω T (RingStage.integral E) ⋙
      integralScalarExtensionOfUniverses l E.carrier L.carrier i T)
    (integralScalar_normalized : ∀
      (E L : FieldStage.{u} l)
      (i : E.carrier →ₐ[Padic l] L.carrier)
      (K : C.{u} l Ω T (.integral E)),
      HEq ((bundle (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i)
      (Allowed.integral E L i)).scalar.realization.inv.app K)
      ((completedScalarComparison l E.carrier L.carrier i T).app K.obj))
    (tor_interval : ∀
      (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (K : C.{u} l Ω T (.integral E)) (a b : ℤ)
      (_h : ∀ n : ℕ, HasProEtaleTorAmplitude T
      (Padic.coefficientExtensionRing l E.carrier (n + 1))
      ((scalarReductionDerivedExtension l E.carrier T n).obj K.obj) a b),
      ∀ n : ℕ, HasProEtaleTorAmplitude T
      (Padic.coefficientExtensionRing l L.carrier (n + 1))
      ((scalarReductionDerivedExtension l L.carrier T n).obj
      ((bundle (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i)
      (Allowed.integral E L i)).scalar.functor.obj K).obj) a b) :
    Nonempty (ScalarRestrictions l Ω T) :=
  ⟨{
    scalar := fun a ha ↦ (bundle a ha).scalar
    scalarShift := fun a ha ↦ (bundle a ha).shift
    finiteScalar_eq := finiteScalar_eq
    finiteScalar_normalized := finiteScalar_normalized
    integralScalar_eq := integralScalar_eq
    integralScalar_normalized := integralScalar_normalized
    tor_interval := tor_interval }⟩

-- Coefficient presentations and full-subcategory instances need this reduction budget.
/-- Scalar restrictions exist independently of any exceptional operation.
Source: Zheng, Construction 4.1 and Propositions 5.24 and 5.26.

Proof: on finite targets, restrict ordinary derived extension literally. Integral
reductions are finite-Tor constructible by their defining reductions; finite coefficient
changes preserve constructibility and the same Tor interval, using bounded flat etale
models. The tensor associator handles composite changes and the tensor unitor handles
identities. At a completed target, identify an allowed map with its induced integral
coefficient embedding and restrict the published strict-tower extension. The finite-free
completed comparison is invertible on derived-complete inputs and supplies the inverse
realization. Its normalized finite reductions give constructibility and the unchanged
Tor interval. Choose the inherited exact shift via the full inclusion so that this
realization commutes with shifts. The construction uses actual coefficient maps, hence
is independent of the Allowed proof and has the prescribed canonical realization for
every completed generator. Positive levels include the residue level; the empty scheme
is handled by the same full-subcategory restriction.
(blueprint: lem-sf-integral-scalar-restrictions). -/
theorem scalarRestrictions_exists (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))] :
    Nonempty (ScalarRestrictions l Ω T) := by
  exact assembleScalarRestrictions l Ω T
    (fun a ha ↦ frozenBundle l Ω D hl T a ha)
    (fun E n a ha ↦ (frozenBundle_finite_facts l Ω D hl T E n a ha).functor_eq)
    (fun E n a ha ↦ (frozenBundle_finite_facts l Ω D hl T E n a ha).normalized)
    (fun E L i ↦ (frozenBundle_integral_facts l Ω D hl T E L i).functor_eq)
    (fun E L i K ↦ (frozenBundle_integral_facts l Ω D hl T E L i).normalized K)
    (fun E L i K a b h n ↦
      (frozenBundle_integral_facts l Ω D hl T E L i).tor_interval K a b h n)

end WeilConjectures.ExceptionalIntegralScalar
