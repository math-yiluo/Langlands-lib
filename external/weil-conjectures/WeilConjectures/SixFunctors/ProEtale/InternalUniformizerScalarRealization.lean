/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PrincipalReductionConeCalculus
public import WeilConjectures.CategoryTheory.RingedSingletonKoszulCone
public import WeilConjectures.SixFunctors.ProEtale.InternalQuotientTowerModel
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatConstantScalarMono
import all WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
import WeilConjectures.SixFunctors.ProEtale.OrdinaryUniformizerScalarComparison

/-! # The regular uniformizer section and its prescribed scalar realization

Source: Stacks Project, algebraization.tex, Lemma derived-completion-koszul (0A0E),
and the constant coefficient identification in integral-models proof (1).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
namespace AlgebraicGeometry.ProEtale.InternalCompletionTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

open IntegralModelsStacks

private theorem uniformizerSection_kernel
    (e : IntegralConstantCompletion.constantRing l E X ≅ ring l E X)
    (f : IntegralConstantCompletion.finiteRing l E X 0 ≅
      smallRing X (condensedRingObj
        (discreteObj (Padic.coefficientExtensionRing l E 1)) X))
    (hf : IntegralConstantCompletion.quotientMap l E X false 0 ≫ f.hom =
      e.hom ≫ residue l E X)
    (V : Scheme.coefficientProEtaleSiteModel.{u, u} X) :
    (ConstantCompletion.kernelIdeal (residue l E X)).sections V =
      Ideal.span {(ConstantCompletion.algebraSection e.hom
        (ULift.up (Padic.coefficientExtensionUniformizer l E))).val (op V)} := by
  have hK : (ConstantCompletion.kernelIdeal (residue l E X)).sections V =
      RingHom.ker ((residue l E X).hom.app (op V)).hom :=
    (ConstantCompletion.kernelIdeal_existsUnique (residue l E X)).exists.choose_spec V
  rw [hK]
  have hk := IntegralConstantCompletion.finite_kernel l E X false 0 V
  simp only [Nat.zero_add, pow_one] at hk
  have hs : RingHom.ker ((residue l E X).hom.app (op V)).hom =
      Ideal.map (e.hom.hom.app (op V)).hom
        (RingHom.ker ((IntegralConstantCompletion.quotientMap l E X false 0).hom.app
          (op V)).hom) := by
    ext x
    rw [Ideal.mem_map_iff_of_surjective _ (ConcreteCategory.bijective_of_isIso
      (e.hom.hom.app (op V))).surjective]
    constructor
    · intro hx
      refine ⟨e.inv.hom.app (op V) x, ?_, ?_⟩
      · change (IntegralConstantCompletion.quotientMap l E X false 0).hom.app (op V)
          (e.inv.hom.app (op V) x) = 0
        apply (ConcreteCategory.bijective_of_isIso (f.hom.hom.app (op V))).injective
        have hh := ConcreteCategory.congr_hom
          (congrArg (fun q ↦ q.hom.app (op V)) hf) (e.inv.hom.app (op V) x)
        change f.hom.hom.app (op V)
          ((IntegralConstantCompletion.quotientMap l E X false 0).hom.app (op V)
            (e.inv.hom.app (op V) x)) =
          (residue l E X).hom.app (op V)
            (e.hom.hom.app (op V) (e.inv.hom.app (op V) x)) at hh
        have he : e.hom.hom.app (op V) (e.inv.hom.app (op V) x) = x :=
          ConcreteCategory.congr_hom
            (congrArg (fun q ↦ q.hom.app (op V)) e.inv_hom_id) x
        rw [he, hx] at hh
        simpa only [map_zero] using hh
      · exact ConcreteCategory.congr_hom
          (congrArg (fun q ↦ q.hom.app (op V)) e.inv_hom_id) x
    · rintro ⟨y, hy, rfl⟩
      change (residue l E X).hom.app (op V) (e.hom.hom.app (op V) y) = 0
      have hh := ConcreteCategory.congr_hom
        (congrArg (fun q ↦ q.hom.app (op V)) hf) y
      change f.hom.hom.app (op V)
        ((IntegralConstantCompletion.quotientMap l E X false 0).hom.app (op V) y) =
        (residue l E X).hom.app (op V) (e.hom.hom.app (op V) y) at hh
      change (IntegralConstantCompletion.quotientMap l E X false 0).hom.app (op V) y = 0
        at hy
      rw [hy, map_zero] at hh
      exact hh.symm
  rw [hs, hk, Ideal.map_span, Set.image_singleton]
  rfl

private theorem uniformizerSection_regular
    (e : IntegralConstantCompletion.constantRing l E X ≅ ring l E X)
    (V : Scheme.coefficientProEtaleSiteModel.{u, u} X) :
    Function.Injective (fun x : (ring l E X).obj.obj (op V) ↦
      (ConstantCompletion.algebraSection e.hom
        (ULift.up (Padic.coefficientExtensionUniformizer l E))).val (op V) * x) := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hne : Padic.coefficientExtensionUniformizer l E ≠ 0 := by
    intro hz
    have hm : Padic.coefficientExtensionMaximalIdeal l E ≠ ⊥ :=
      h.2.2.2.2.2.2.2.2.2.1
    exact hm (by rw [← hgen, hz, Ideal.span_singleton_eq_bot])
  have ha : Function.Injective (fun x : ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l E) ↦
        ULift.up (Padic.coefficientExtensionUniformizer l E) * x) := by
    intro x y hxy
    apply ULift.ext
    exact mul_left_cancel₀ hne (congrArg ULift.down hxy)
  have hinj := SheafOfModules.constantScalar_ring_injective
    (IntegralConstantCompletion.topology X)
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
    (ULift.up (Padic.coefficientExtensionUniformizer l E)) ha V
  have he := ConcreteCategory.bijective_of_isIso (e.hom.hom.app (op V))
  intro x y hxy
  obtain ⟨x, rfl⟩ := he.surjective x
  obtain ⟨y, rfl⟩ := he.surjective y
  apply congrArg (e.hom.hom.app (op V))
  apply hinj
  apply he.injective
  simpa only [map_mul, ConstantCompletion.constantSection] using (show
    e.hom.hom.app (op V) _ * e.hom.hom.app (op V) x =
      e.hom.hom.app (op V) _ * e.hom.hom.app (op V) y from hxy)

local instance scalarModulesMonoidal :
    MonoidalCategory (ConstantCompletion.Mod (ring l E X)) :=
  SheafOfModules.monoidalCategory (ring l E X)
local instance ordinaryModulesSymmetric :
    SymmetricCategory (ConstantCompletion.Mod (ring l E X)) :=
  SheafOfModules.symmetricCategory (ring l E X)
local instance ordinaryModulesPreadditive :
    MonoidalPreadditive (ConstantCompletion.Mod (ring l E X)) :=
  Classical.choice (SheafOfModules.tensorClosed (ring l E X)).1
local instance ordinaryModulesClosed :
    MonoidalClosed (ConstantCompletion.Mod (ring l E X)) :=
  Classical.choice (SheafOfModules.tensorClosed (ring l E X)).2.1
local instance ordinaryModulesGrothendieck :
    IsGrothendieckAbelian.{u + 1} (ConstantCompletion.Mod (ring l E X)) :=
  SheafOfModules.isGrothendieckAbelian _

private theorem intertwine_pow {C : Type*} [Category C] {A B : C}
    (a : End A) (b : End B) (v : A ⟶ B) (h : a.asHom ≫ v = v ≫ b.asHom) (k : ℕ) :
    (a ^ k).asHom ≫ v = v ≫ (b ^ k).asHom := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        (a ^ (k + 1)).asHom ≫ v = a.asHom ≫ ((a ^ k).asHom ≫ v) := by
          rw [pow_succ, End.mul_asHom, Category.assoc]
        _ = a.asHom ≫ (v ≫ (b ^ k).asHom) := by rw [ih]
        _ = v ≫ (b ^ (k + 1)).asHom := by
          rw [← Category.assoc, h, Category.assoc, pow_succ, End.mul_asHom]

private theorem scalarOnModules_pow
    (d : End (Mod.regular (DerivedNakayama.integerRing l E))) (k : ℕ) :
    DerivedNakayama.scalarOnModules l E X (d ^ k) =
      ((End.of (DerivedNakayama.scalarOnModules l E X d)) ^ k).asHom := by
  let A := AdicCompletion.Modules l E X
  let F₁ := (DerivedNakayama.pullback l E X).mapEnd
    (Mod.regular (DerivedNakayama.integerRing l E))
  let F₂ := (DerivedNakayama.regularPullbackIso l E X).conj.toMonoidHom
  let F₃ := (tensoringLeft A).mapEnd (𝟙_ A)
  let F₄ := (leftUnitorNatIso A).conj.toMonoidHom
  exact congrArg End.asHom ((F₄.comp (F₃.comp (F₂.comp F₁))).map_pow d k)

private theorem scalarOnModules_map_pow
    (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (M : AdicCompletion.Modules l E X) (k : ℕ) :
    (modules l E X).map ((DerivedNakayama.scalarOnModules l E X (d ^ k)).app M) =
      ((End.of ((modules l E X).map
        ((DerivedNakayama.scalarOnModules l E X d).app M))) ^ k).asHom := by
  rw [scalarOnModules_pow]
  let τ : End (𝟭 (AdicCompletion.Modules l E X)) :=
    .of (DerivedNakayama.scalarOnModules l E X d)
  change (modules l E X).map ((τ ^ k).asHom.app M) =
    ((End.of ((modules l E X).map (τ.asHom.app M))) ^ k).asHom
  induction k with
  | zero => simp
  | succ k ih =>
      simpa only [pow_succ, End.mul_asHom, NatTrans.comp_app, Functor.map_comp,
        End.of] using congrArg (fun z ↦ (modules l E X).map (τ.asHom.app M) ≫ z) ih

private theorem complex_scalar_unitor
    (P : ringedSiteComplex (ring l E X)) (f : End P)
    (a : End (𝟙_ (ConstantCompletion.Mod (ring l E X))))
    (h : ∀ q : ℤ, f.asHom.f q ≫ (ρ_ (P.X q)).inv =
      (ρ_ (P.X q)).inv ≫ P.X q ◁ a.asHom) :
    f.asHom ≫ (ringedKoszulRightUnitIso (ring l E X) P).inv =
      (ringedKoszulRightUnitIso (ring l E X) P).inv ≫
        ((ringedKoszulTensor (ring l E X)).obj P).map
          ((HomologicalComplex.single _ (.up ℤ) 0).map a.asHom) := by
  ext q : 1
  change f.asHom.f q ≫ (HomologicalComplex.rightUnitor' P).inv q =
    (HomologicalComplex.rightUnitor' P).inv q ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 P)
        ((HomologicalComplex.single _ (.up ℤ) 0).map a.asHom)
        (curriedTensor _) (.up ℤ)).f q
  rw [HomologicalComplex.rightUnitor'_inv]
  simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.id_f, HomologicalComplex.single_map_f_self,
    curriedTensor_map_app, id_whiskerRight, curriedTensor_obj_map]
  rw [← Category.assoc, h q]
  erw [Category.id_comp]
  simp only [Category.assoc, ← whiskerLeft_comp_assoc, Iso.inv_hom_id_assoc]

/-- The constant uniformizer is a regular generator of the residue kernel and realizes
scalar multiplication under the prescribed ordinary module transport. This assertion
involves no other generator and no variable change of basis.

Source: Stacks Project, algebraization.tex, Lemma derived-completion-koszul (0A0E),
and integral-models proof (1), constant coefficient comparison.
(auxiliary; not a blueprint node).

Proof: use the canonical constant-sheaf/inverse-image comparison on the integer ring
and its first quotient, followed by reconstruction of section rings and restriction
along AsSmall.down. Apply the resulting ring map to the constant uniformizer section.
The quotient square identifies its principal ideal with the kernel of the residue
map. Multiplication by the uniformizer is injective on the coefficient DVR. Exact
constant sheafification, inverse image, and the section-module equivalence preserve
this injection, so it remains injective on sections of every object of the small
site. For the action formula, extensionality on continuous functions and hd identify
d with the canonical uniformizer endomorphism of the point regular module. Pullback
and the pointComparison identify its action with multiplication by this constant
section. Restriction of scalars keeps the underlying additive maps; the section
module equivalence keeps their actual section actions. Powers therefore give the
same assertion for d^(n+1). In the total tensor with the complex O[0], the right
unitor removes the rank-one factor, and the tensor of its scalar endomorphism acts
by precisely this section power. Check the equation on each coproduct summand of
the total tensor; only the summand with second degree zero is nonzero. The formulas
are natural in all terms of P and commute with its differential, so hold without
boundedness or flatness. For the empty scheme or zero complex the same statements
hold for the unique maps, with no nontriviality assumption on section rings. -/
theorem uniformizer_scalar_realization :
    ∃ t : ((ring l E X).obj ⋙ forget CommRingCat).sections,
      (∀ U : Scheme.coefficientProEtaleSiteModel.{u, u} X,
        (ConstantCompletion.kernelIdeal (residue l E X)).sections U =
          Ideal.span {t.val (op U)}) ∧
      (∀ U : Scheme.coefficientProEtaleSiteModel.{u, u} X,
        Function.Injective (fun x : (ring l E X).obj.obj (op U) ↦ t.val (op U) * x)) ∧
      ∀ (d : End (Mod.regular (DerivedNakayama.integerRing l E))),
        (∀ (S : Profinite.{u}ᵒᵖ) (b : (DerivedNakayama.integerRing l E).obj.obj S)
          (s : S.unop), ((d.asHom.hom.hom.app S) b).down s =
            Padic.coefficientExtensionUniformizer l E * b.down s) →
        ∀ (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) (n : ℕ),
          ((modules l E X).mapHomologicalComplex (.up ℤ)).map
              (PrincipalReduction.scalar l E X d n P) ≫
              (ringedKoszulRightUnitIso (ring l E X) (complex l E X P)).inv =
            (ringedKoszulRightUnitIso (ring l E X) (complex l E X P)).inv ≫
              (ringedSingletonKoszulPower (ring l E X) t (complex l E X P) n).asHom := by
  obtain ⟨e, f, hf, hscalar⟩ := ordinary_uniformizer_scalar_comparison l E X
  let t := ConstantCompletion.algebraSection e.hom
    (ULift.up (Padic.coefficientExtensionUniformizer l E))
  refine ⟨t, uniformizerSection_kernel l E X e f hf,
    uniformizerSection_regular l E X e, ?_⟩
  intro d hd P n
  let a := ringedKoszulScalar (ring l E X) t
  have hp (M : AdicCompletion.Modules l E X) :
      (modules l E X).map
          ((DerivedNakayama.scalarOnModules l E X (d ^ (n + 1))).app M) ≫
          (ρ_ ((modules l E X).obj M)).inv =
        (ρ_ ((modules l E X).obj M)).inv ≫
          (modules l E X).obj M ◁ (a ^ (n + 1)).asHom := by
    rw [scalarOnModules_map_pow]
    have hm := congrArg End.asHom (map_pow
      (((curriedTensor (ConstantCompletion.Mod (ring l E X))).obj
        ((modules l E X).obj M)).mapEnd (𝟙_ _)) a (n + 1))
    change (modules l E X).obj M ◁ (a ^ (n + 1)).asHom =
      ((End.of ((modules l E X).obj M ◁ a.asHom)) ^ (n + 1)).asHom at hm
    rw [hm]
    exact intertwine_pow _ _ _ (hscalar d hd M) (n + 1)
  unfold ringedSingletonKoszulPower
  apply complex_scalar_unitor l E X (complex l E X P) (.of _) (a ^ (n + 1))
  intro q
  exact hp (P.X q)

end AlgebraicGeometry.ProEtale.InternalCompletionTransport
