/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

/-! # The coefficient module of one uniformizer layer

Source: Serre, Local Fields, Chapter I, section 1, and the scalar residue-layer
argument of the blueprint. Multiplication by a uniformizer power identifies a
successive layer with the first quotient, with its actual quotient coefficient action.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The first coefficient quotient is a field because its defining ideal is maximal.
Source: Serre, Local Fields, Chapter I, section 1.
(blueprint: lem-sf-integral-scalar-residue-coefficient-iso). -/
@[reducible] noncomputable instance integralScalarResidueField :
    Field (Padic.coefficientExtensionRing l E 1) := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hmax : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
  have hm : (Padic.coefficientExtensionIdeal l E 1).IsMaximal := by
    change (Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1).IsMaximal
    rw [pow_one, hgen]
    exact hmax
  exact @Ideal.Quotient.field _ _ _ hm

/-- Reduction from a positive quotient to the residue quotient.
Source: Serre, Local Fields, Chapter I, section 1.
(blueprint: lem-sf-integral-scalar-residue-coefficient-iso). -/
def integralScalarResidueRingProjection (n : ℕ) :
    Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l E 1 :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : 1 ≤ n + 1))

variable (Y : AlgebraicGeometry.Scheme.{u})

/-- The constant ring-sheaf residue projection.
Source: Serre, Local Fields, Chapter I, section 1.
(blueprint: lem-sf-integral-scalar-residue-coefficient-iso). -/
def integralScalarResidueProjection (n : ℕ) :
    integralCoefficientCommRingSheaf l E Y n ⟶ integralCoefficientCommRingSheaf l E Y 0 :=
  (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1}
      (integralScalarResidueRingProjection l E n)))

private theorem residueProjection_zero :
    integralScalarResidueProjection l E Y 0 = 𝟙 _ := by
  unfold integralScalarResidueProjection
  convert (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map_id
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))) using 1 <;>
    try rfl
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  cases x with
  | up x =>
    induction x using Quotient.inductionOn' with
    | h x => rfl

private theorem residueProjection_succ (n : ℕ) :
    unrestrictedCoefficientStep l E Y n ≫ integralScalarResidueProjection l E Y n =
      integralScalarResidueProjection l E Y (n + 1) := by
  rw [unrestrictedCoefficientStep, integralScalarResidueProjection,
    integralScalarResidueProjection, ← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  cases x with
  | up x =>
    induction x using Quotient.inductionOn' with
    | h x => rfl

private theorem completed_residue_projection (n : ℕ) :
    completedIntegralCommRingProjectionUnrestricted l E Y n ≫
      integralScalarResidueProjection l E Y n =
        completedIntegralCommRingProjectionUnrestricted l E Y 0 := by
  induction n with
  | zero => rw [residueProjection_zero, Category.comp_id]
  | succ n ih =>
    rw [← residueProjection_succ, ← Category.assoc, unrestrictedCoefficientStep_comp, ih]

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

private theorem scalar_residue_projection (n : ℕ) :
    integralScalarQuotientSheafMap l E L ι Y n ≫
      integralScalarResidueProjection l L Y n =
    integralScalarResidueProjection l E Y n ≫
      integralScalarQuotientSheafMap l E L ι Y 0 := by
  unfold integralScalarQuotientSheafMap integralScalarResidueProjection
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  cases x with
  | up x =>
    induction x using Quotient.inductionOn' with
    | h x => rfl

/-- The action on a target residue layer factors through the source residue quotient.
Source: the defining limit projections and the quotient map of integer rings.
(blueprint: lem-sf-integral-scalar-residue-coefficient-iso). -/
theorem integralScalarResidue_triangle (n : ℕ) :
    completedIntegralCommRingProjectionUnrestricted l E Y 0 ≫
      integralScalarQuotientSheafMap l E L ι Y 0 =
    integralScalarRho l E L ι Y n ≫ integralScalarResidueProjection l L Y n := by
  rw [integralScalarRho, Category.assoc, scalar_residue_projection,
    ← Category.assoc, completed_residue_projection]

private theorem principalLayerIso
    {R : Type v} {B k : Type (u + 1)} [CommRing R] [IsDomain R] [CommRing B] [CommRing k]
    (x : R) (hx : x ≠ 0) (N j : ℕ) (hj : j + 1 ≤ N)
    (z : R →+* B) (hz : Function.Surjective z) (q : B →+* k)
    (hq : Function.Surjective q)
    (hzker : ∀ r : R, z r = 0 ↔ x ^ N ∣ r)
    (hqker : ∀ r : R, q (z r) = 0 ↔ x ∣ r) :
    let t := z x
    let I : Ideal B := Ideal.span {t} ^ j
    let J := Submodule.comap I.subtype (Ideal.span {t} ^ (j + 1) : Submodule B B)
    Nonempty (ModuleCat.of B (I ⧸ J) ≅
      (ModuleCat.restrictScalars q).obj (ModuleCat.of k k)) := by
  let t := z x
  let I : Ideal B := Ideal.span {t} ^ j
  let J := Submodule.comap I.subtype (Ideal.span {t} ^ (j + 1) : Submodule B B)
  let g : B →ₗ[B] I := (LinearMap.mulRight B (t ^ j)).codRestrict I (by
    intro a
    change a * t ^ j ∈ Ideal.span {t} ^ j
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact dvd_mul_left _ _)
  let f : B →ₗ[B] I ⧸ J := J.mkQ.comp g
  let kB := (ModuleCat.restrictScalars q).obj (ModuleCat.of k k)
  let ql : B →ₗ[B] kB :=
    { toFun := q
      map_add' := q.map_add
      map_smul' := q.map_mul }
  have hker (a : B) : f a = 0 ↔ q a = 0 := by
    obtain ⟨r, rfl⟩ := hz a
    change J.mkQ (g (z r)) = 0 ↔ q (z r) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hqker]
    change z r * t ^ j ∈ Ideal.span {t} ^ (j + 1) ↔ x ∣ r
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨s, rfl⟩ := hz b
      have he : z ((r - x * s) * x ^ j) = 0 := by
        rw [map_mul, map_sub, map_mul, map_pow]
        change (z r - t * z s) * t ^ j = 0
        calc
          (z r - t * z s) * t ^ j = z r * t ^ j - t ^ (j + 1) * z s := by ring
          _ = 0 := sub_eq_zero.mpr hb
      have hd : x ^ (j + 1) ∣ (r - x * s) * x ^ j :=
        (pow_dvd_pow x hj).trans ((hzker _).mp he)
      have hd' : x ∣ r - x * s :=
        (mul_dvd_mul_iff_right (pow_ne_zero j hx)).mp (by
          simpa only [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hd)
      simpa only [sub_add_cancel] using dvd_add hd' (dvd_mul_right x s)
    · rintro ⟨s, rfl⟩
      refine ⟨z s, ?_⟩
      rw [map_mul]
      change t * z s * t ^ j = t ^ (j + 1) * z s
      ring
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective J y
    have hv : t ^ j ∣ (v : B) := by
      simpa only [I, Ideal.span_singleton_pow, Ideal.mem_span_singleton] using v.property
    obtain ⟨a, ha⟩ := hv
    refine ⟨a, ?_⟩
    change J.mkQ (g a) = J.mkQ v
    congr 1
    apply Subtype.ext
    change a * t ^ j = (v : B)
    simpa only [mul_comm] using ha.symm
  have hk : LinearMap.ker f = LinearMap.ker ql := by
    ext a
    exact hker a
  exact ⟨((f.quotKerEquivOfSurjective hsurj).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hk ≪≫ₗ ql.quotKerEquivOfSurjective hq).toModuleIso⟩

private theorem constantRestrictedUnitIso
    (B k : Type (u + 1)) [CommRing B] [CommRing k] (q : B →+* k) :
    let b := (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom q)
    Nonempty ((adicLisseConstantModules Y B).obj
      ((ModuleCat.restrictScalars q).obj (ModuleCat.of k k)) ≅
        (pbcRestrict b).obj (SheafOfModules.unit (adicLisseRing Y k))) := by
  let J := ProEt.topology Y
  let : HasSheafify J AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} Y
  let : J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} Y
  let : HasSheafify J CommRingCat.{u + 1} :=
    integralCoefficientRingSheafify.{u, 0} Y
  let b := (constantSheaf J CommRingCat.{u + 1}).map (CommRingCat.ofHom q)
  let η : (Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of k) ⟶
      (adicLisseConstantRing Y k).obj :=
    toSheafify J ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of k))
  let P : PresheafOfModules.{u + 1}
      ((Functor.const Y.ProEtᵒᵖ).obj (RingCat.of B)) :=
    ((siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) B) ⋙
    PresheafOfModules.pushforward₀
      ((Functor.const Y.ProEt).obj (Discrete.mk (ULift.up ())))
      ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of B))).obj
        ((ModuleCat.restrictScalars q).obj (ModuleCat.of k k))
  let M : pbcModules Y (adicLisseConstantRing Y B) :=
    (pbcRestrict b).obj (SheafOfModules.unit (adicLisseRing Y k))
  let g : P ⟶ (PresheafOfModules.restrictScalars (adicLisseConstantUnit Y B)).obj
      M.val :=
    { app := fun V ↦ ModuleCat.ofHom
        (X := P.obj V)
        (Y := ((PresheafOfModules.restrictScalars
          (adicLisseConstantUnit Y B)).obj M.val).obj V)
        { toFun := (η.app V).hom
          map_add' := (η.app V).hom.map_add
          map_smul' := fun r c ↦ by
            change (η.app V).hom (q r * (show k from c)) =
              (b.hom.app V).hom (((adicLisseConstantUnit Y B).app V).hom r) *
                (η.app V).hom c
            rw [map_mul]
            congr 1
            exact ConcreteCategory.congr_hom
              (congr_app (toSheafify_naturality J
                ((Functor.const Y.ProEtᵒᵖ).map (CommRingCat.ofHom q))) V) r }
      naturality := by
        intro U V a
        ext c
        exact ConcreteCategory.congr_hom (η.naturality a) c }
  let h : (PresheafOfModules.sheafification.{u + 1, u, u + 1, u + 1}
      (adicLisseConstantUnit Y B)).obj P ⟶ M :=
    (PresheafOfModules.sheafificationHomEquiv.{u + 1, u, u + 1, u + 1}
      (adicLisseConstantUnit Y B) (P := P) (F := M)).symm g
  let g₀ : (Y.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
    (PresheafOfModules.toPresheaf _).obj P
  let g₁ : g₀ ⟶ (PresheafOfModules.toPresheaf _).obj
      ((PresheafOfModules.restrictScalars (adicLisseConstantUnit Y B)).obj M.val) :=
    (PresheafOfModules.toPresheaf _).map g
  have hinj : Presheaf.IsLocallyInjective J g₁ :=
    (Presheaf.isLocallyInjective_forget_iff J g₁).mp
      (inferInstanceAs (Presheaf.IsLocallyInjective J
        (Functor.whiskerRight η (forget CommRingCat.{u + 1}))))
  have hsurj : Presheaf.IsLocallySurjective J g₁ :=
    (Presheaf.isLocallySurjective_iff_whisker_forget J g₁).mpr
      (inferInstanceAs (Presheaf.IsLocallySurjective J
        (Functor.whiskerRight η (forget CommRingCat.{u + 1}))))
  have hW : J.W g₁ := (J.W_iff_isLocallyBijective g₁).mpr ⟨hinj, hsurj⟩
  have : IsIso ((presheafToSheaf J AddCommGrpCat.{u + 1}).map g₁) := (J.W_iff g₁).mp hW
  have : IsIso ((SheafOfModules.toSheaf.{u + 1} _).map h) := by
    dsimp only [h]
    erw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm.{u + 1, u, u + 1, u + 1}
        (adicLisseConstantUnit Y B) (P := P) (F := M) g,
      (sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv_counit]
    infer_instance
  have : IsIso h := isIso_of_reflects_iso _ (SheafOfModules.toSheaf.{u + 1} _)
  exact ⟨asIso h⟩

/-- A uniformizer-filtration layer is the restricted regular residue module sheaf.
This is a statement about coefficients alone, independent of any complex or interval.
Source: Serre, Local Fields, Chapter I, section 1; the multiplication-and-cancellation
step in lem-sf-integral-scalar-residue-layers.
(blueprint: lem-sf-integral-scalar-residue-coefficient-iso).
Proof: put A = O_L and pi equal to its chosen uniformizer. Multiplication by pi^j
maps A onto (pi^j)/(pi^(j+1)). Its kernel is (pi): divisibility of pi^j*x by
pi^(j+1) allows cancellation of the nonzero pi^j in the domain A. Passing first to
A/(pi^(n+1)) gives the displayed layer, because j < n+1 and the extra ideal
(pi^(n+1)) is contained in (pi^(j+1)). These maps therefore identify the layer with
A/(pi), linearly over B via the quotient projection. Apply the constant module
sheaf functor to this module isomorphism. Restriction of scalars commutes with
constant sheafification, since its underlying additive sheafification is the same,
and the constant regular residue module is the residue ring sheaf unit. Compose
these isomorphisms. For n=0 and j=0 the map is the usual quotient unit map;
no cancellation by zero occurs, and the empty scheme presents no exception. -/
theorem integralScalarResidueCoefficientIso (n : ℕ)
    (F : Fin (n + 1 + 1) → Submodule
      (ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1)))
      (ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))))
    (hF : F = fun (j : Fin (n + 1 + 1)) ↦ (Ideal.span ({ULift.up ((Ideal.Quotient.mk
      (Padic.coefficientExtensionIdeal l L (n + 1)))
        (Padic.coefficientExtensionUniformizer l L))} :
          Set (ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))))) ^ (j : ℕ))
    (j : Fin (n + 1)) :
    let B := ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))
    Nonempty ((adicLisseConstantModules Y B).obj
      (ModuleCat.of B ((F j.castSucc) ⧸ (F j.succ).comap (F j.castSucc).subtype)) ≅
        (pbcRestrict (integralScalarResidueProjection l L Y n)).obj
          (SheafOfModules.unit (integralCoefficientSheaf l L Y 0))) := by
  subst F
  let B := ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))
  let k := ULift.{u + 1} (Padic.coefficientExtensionRing l L 1)
  let x := Padic.coefficientExtensionUniformizer l L
  let z : Padic.coefficientExtensionIntegers l L →+* B :=
    (ULift.ringEquiv : B ≃+* _).symm.toRingHom.comp
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (n + 1)))
  let q : B →+* k := RingHom.ulift.{u + 1, u + 1}
    (integralScalarResidueRingProjection l L n)
  have h := (Padic.coefficientExtensionIntegers_dvr l L).choose_spec
  have hgen : Ideal.span {x} = Padic.coefficientExtensionMaximalIdeal l L :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hx : x ≠ 0 := by
    intro hzero
    rw [hzero, Ideal.span_singleton_zero] at hgen
    exact h.2.2.2.2.2.2.2.2.2.1 hgen.symm
  have hz : Function.Surjective z := by
    intro b
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective b.down
    exact ⟨r, ULift.ext hr⟩
  have hq : Function.Surjective q := by
    intro c
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective c.down
    refine ⟨z r, ?_⟩
    apply ULift.ext
    exact hr
  have hzker (r : Padic.coefficientExtensionIntegers l L) :
      z r = 0 ↔ x ^ (n + 1) ∣ r := by
    change (ULift.up (Ideal.Quotient.mk _ r) : B) = ULift.up 0 ↔ _
    rw [ULift.up_inj, Ideal.Quotient.eq_zero_iff_mem]
    simp only [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, x]
  have hqker (r : Padic.coefficientExtensionIntegers l L) : q (z r) = 0 ↔ x ∣ r := by
    change (ULift.up (Ideal.Quotient.mk _ r) : k) = ULift.up 0 ↔ _
    rw [ULift.up_inj, Ideal.Quotient.eq_zero_iff_mem]
    simp only [Padic.coefficientExtensionIdeal, pow_one, Ideal.mem_span_singleton, x]
  obtain ⟨e⟩ := principalLayerIso x hx (n + 1) (j : ℕ) (by omega) z hz q hq hzker hqker
  obtain ⟨e'⟩ := constantRestrictedUnitIso Y B k q
  exact ⟨(adicLisseConstantModules Y B).mapIso e ≪≫ e'⟩

end WeilConjectures
