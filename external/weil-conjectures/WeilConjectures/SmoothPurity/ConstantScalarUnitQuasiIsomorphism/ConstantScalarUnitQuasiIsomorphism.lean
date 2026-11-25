/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstantScalarStrictUnit.ConstantScalarStrictUnit
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore

/-! # The regular coefficient scalar unit is a quasi-isomorphism

Source: Bhatt--Scholze, Propositions 3.1.10, 3.2.3(1), 4.2.8,
Definition 3.5.2 and Lemma 6.8.2(1)
(blueprint: lem-weil-constant-scalar-unit-quasi-isomorphism).

Positive exponent m is indexed by n = m-1. The strict tower, tensor,
normalized unit and mapping cocone are those of the recorded dependencies.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ConstantScalarUnitQuasiIsomorphism
open ConstantScalarStrictUnit

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : Scheme.{t})

/-- The actual restricted quotient tower of the regular source complex.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-weil-constant-scalar-unit-quasi-isomorphism). -/
abbrev tower := (integralScalarTowerFunctor l E L ι Y).obj (regularComplex l E Y)

/-- Its termwise product B, before localization.
Source: Bhatt--Scholze, Proposition 3.1.10
(blueprint: lem-weil-constant-scalar-unit-quasi-isomorphism). -/
abbrev product := ∏ᶜ (fun n : ℕ ↦ (tower l E L ι Y).obj (op n))

/-- The first component of the specified normalized unit.
Source: Bhatt--Scholze, Lemma 6.8.2(1), strict coordinate refinement
(blueprint: lem-weil-constant-scalar-unit-quasi-isomorphism). -/
def inclusion (η : regularComplex l L Y ⟶
    (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y)) :
    regularComplex l L Y ⟶ product l E L ι Y :=
  η ≫ CochainComplex.mappingCocone.fst (boundary l E Y L ι)

/-- The prescribed quotient leg u_n inverse composed with pi_n.
Its tensor formula is fixed by quotientCoordinates, rather than a choice of isomorphism.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-weil-constant-scalar-unit-quasi-isomorphism). -/
def leg (η : regularComplex l L Y ⟶
    (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y)) (n : ℕ) :=
  inclusion l E L ι Y η ≫ Pi.π (fun m : ℕ ↦ (tower l E L ι Y).obj (op m)) n

-- The pure-tensor and functor APIs below do not need the existence witnesses unfolded.
attribute [local irreducible] integralScalarReductionWitness scalarReductionExistence
  scalarReductionDerivedExistence unrestrictedIntegralReductionExistence

private theorem transition_locallySurjective (n : ℕ) :
    Sheaf.IsLocallySurjective (integralCoefficientSheafTransition l L Y n) := by
  let J := Scheme.ProEt.topology Y
  let : HasSheafify J CommRingCat.{max u (t + 1)} :=
    integralCoefficientRingSheafify Y
  let : HasWeakSheafify J CommRingCat.{max u (t + 1)} :=
    (integralCoefficientRingSheafify.{t, u} Y).isRightAdjoint
  let : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf _
  let : J.WEqualsLocallyBijective CommRingCat.{max u (t + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let f : CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionRing l L (n + 1 + 1))) ⟶
      CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l L (n + 1))) :=
    CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
      ((Padic.coefficientExtensionTransition l L (n + 1)).comp
        (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨x, hx⟩ := Ideal.Quotient.factor_surjective
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) z.down
    exact ⟨⟨x⟩, congrArg ULift.up hx⟩
  have hc : Presheaf.IsLocallySurjective J ((Functor.const Y.ProEtᵒᵖ).map f) :=
    Presheaf.isLocallySurjective_of_surjective J _ (fun _ ↦ hf)
  have hs : Sheaf.IsLocallySurjective ((constantSheaf J CommRingCat).map f) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff J _).mpr hc
  constructor
  intro V x
  exact hs.imageSieve_mem x

private theorem countable_exact : CountableAB4Star (integralTowerModules l L Y) := by
  let A := integralTowerModules l L Y
  let : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  have : (lim (J := Discrete ℕ) (C := A)).PreservesEpimorphisms :=
    { preserves := by
        intro F G f hf
        have h := (Scheme.ProEt.countableProducts_exact.{t, u, 0} Y
          (completedIntegralCommRingSheafUnrestricted l L Y)).2.2
          ℕ (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
          (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
        have he : lim.map f = (Limits.Pi.isoLimit _).inv ≫
            Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Limits.Pi.isoLimit _).hom := by
          apply limit.hom_ext
          intro ⟨n⟩
          simp
        rw [he]
        infer_instance }
  have := hasExactLimitsOfShape_of_preservesEpi A (Discrete ℕ)
  exact CountableAB4Star.of_hasExactLimitsOfShape_nat A

private theorem normalized_coordinates
    (u : ∀ n : ℕ, (integralScalarFiniteComplex l E L ι Y n).obj
      (regularComplex l E Y) ≅ finiteRegularComplex l L Y n)
    (hu : ∀ (n : ℕ) (V : Y.ProEt)
      (z : (integralCoefficientSheaf l L Y n).obj.obj (op V)),
      (((finiteZeroIso l L Y n).inv ≫ (u n).inv.f 0).val.app (op V)) z =
        integralScalarTensorSection l E L ι Y n ((regularComplex l E Y).X 0) (op V)
          z (regularSection l E Y V 1))
    (η : regularComplex l L Y ⟶
      (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y))
    (hη : quotientCoordinates l E Y L ι η) (n : ℕ) (V : Y.ProEt)
    (s : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj (op V)) :
    (((u n).hom.f 0 ≫ (finiteZeroIso l L Y n).hom).val.app (op V))
      (((leg l E L ι Y η n).f 0).val.app (op V) (regularSection l L Y V s)) =
        (completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app (op V) s := by
  change (((u n).hom.f 0 ≫ (finiteZeroIso l L Y n).hom).val.app (op V))
    ((coordinate l E Y L ι η n).val.app (op V) (regularSection l L Y V s)) = _
  rw [hη n V s, ← hu n V]
  change (((finiteZeroIso l L Y n).inv ≫ (u n).inv.f 0 ≫
    (u n).hom.f 0 ≫ (finiteZeroIso l L Y n).hom).val.app (op V)) _ = _
  simp only [← HomologicalComplex.comp_f_assoc, Iso.inv_hom_id,
    HomologicalComplex.id_f, Category.id_comp]
  rfl

private abbrev quotientZeroIso
    (F : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l L Y) ℤ)
    (u : ∀ n : ℕ, F.obj (op n) ≅
      (integralOperationsRestrict l L Y n).obj (finiteRegularComplex l L Y n)) (n : ℕ) :=
  (HomologicalComplex.eval _ (.up ℤ) 0).mapIso (u n) ≪≫
    (scalarReductionRestriction l L Y n).mapIso (finiteZeroIso l L Y n)

private theorem quotient_ordinary_limit
    (F : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l L Y) ℤ)
    (u : ∀ n : ℕ, F.obj (op n) ≅
      (integralOperationsRestrict l L Y n).obj (finiteRegularComplex l L Y n))
    (g : ∀ n : ℕ, regularComplex l L Y ⟶ F.obj (op n))
    (hn : ∀ (n : ℕ) (V : Y.ProEt)
      (s : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj (op V)),
      ((quotientZeroIso l L Y F u n).hom.val.app (op V))
        (((g n).f 0).val.app (op V) (regularSection l L Y V s)) =
          (completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app (op V) s)
    (ht : ∀ (n : ℕ) (V : Y.ProEt) (x : ((F.obj (op (n + 1))).X 0).val.obj (op V)),
      ((quotientZeroIso l L Y F u n).hom.val.app (op V))
        (((F.map (homOfLE n.le_succ).op).f 0).val.app (op V) x) =
      (integralCoefficientSheafTransition l L Y n).hom.app (op V)
        (((quotientZeroIso l L Y F u (n + 1)).hom.val.app (op V)) x)) :
    ∃ π : (Functor.const ℕᵒᵖ).obj (regularComplex l L Y) ⟶ F,
      (∀ n : ℕ, π.app (op n) = g n) ∧ Nonempty (IsLimit (Cone.mk _ π)) := by
  have hzero (n : ℕ) (p : ℤ) (hp : p ≠ 0) : IsZero ((F.obj (op n)).X p) := by
    let e := u n
    apply IsZero.of_iso _ ((HomologicalComplex.eval _ _ p).mapIso e)
    exact (SheafOfModules.restrictScalars _).map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ p hp)
  have hcompat (n : ℕ) : g n =
      g (n + 1) ≫ F.map (homOfLE n.le_succ).op := by
    apply HomologicalComplex.hom_ext
    intro p
    by_cases hp : p = 0
    · subst p
      ext V : 2
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      let s := ((regularZeroIso l L Y).hom.val.app V) x
      have hx : regularSection l L Y V.unop s = x := by
        change ((regularZeroIso l L Y).hom ≫ (regularZeroIso l L Y).inv).val.app V x = x
        simp
      let a := (quotientZeroIso l L Y F u n).hom.val.app V
      have ha : Function.Injective a :=
        (ConcreteCategory.bijective_of_isIso
          ((SheafOfModules.evaluation _ V).mapIso
            (quotientZeroIso l L Y F u n)).hom).1
      apply ha
      rw [← hx]
      simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
        PresheafOfModules.comp_app, ModuleCat.comp_apply]
      change a (((g n).f 0).val.app V
          (regularSection l L Y V.unop s)) =
        a ((((F.map (homOfLE n.le_succ).op).f 0).val.app V)
            (((g (n + 1)).f 0).val.app V
              (regularSection l L Y V.unop s)))
      rw [ht n V.unop, hn n V.unop s, hn (n + 1) V.unop s]
      change ((limit.π (integralCoefficientSheafSystem l L Y) (op n)).hom.app V) s =
        ((integralCoefficientSheafTransition l L Y n).hom.app V)
          (((limit.π (integralCoefficientSheafSystem l L Y) (op (n + 1))).hom.app V) s)
      have hw := limit.w (integralCoefficientSheafSystem l L Y)
        (homOfLE n.le_succ).op
      rw [show (integralCoefficientSheafSystem l L Y).map (homOfLE n.le_succ).op =
        integralCoefficientSheafTransition l L Y n from
          Functor.ofOpSequence_map_homOfLE_succ _ n] at hw
      exact (congrArg (fun f ↦ f.hom.app V s) hw).symm
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ p hp).eq_of_src _ _
  let c : Cone F :=
    { pt := regularComplex l L Y
      π := NatTrans.ofOpSequence (fun n ↦ g n) (by
        intro n
        simpa using hcompat n) }
  refine ⟨c.π, fun _ ↦ rfl, ⟨?_⟩⟩
  apply HomologicalComplex.isLimitOfEval
  intro p
  by_cases hp : p = 0
  · subst p
    apply isLimitOfReflects (SheafOfModules.forget _)
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro V
    apply isLimitOfReflects (forget₂ (ModuleCat.{max u (t + 1)}
      ((completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj V))
      AddCommGrpCat.{max u (t + 1)})
    apply isLimitOfReflects (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)})
    let H := F ⋙ HomologicalComplex.eval _ (.up ℤ) 0 ⋙
      SheafOfModules.evaluation _ V ⋙ CategoryTheory.forget _
    let G := integralCoefficientSheafSystem l L Y ⋙
      sheafToPresheaf _ _ ⋙ (evaluation Y.ProEtᵒᵖ RingCat).obj V ⋙
      CategoryTheory.forget RingCat
    let a : H ⟶ G := NatTrans.ofOpSequence
      (fun n ↦ TypeCat.ofHom
        ((quotientZeroIso l L Y F u n).hom.val.app V)) (by
          intro n
          ext x
          rw [show H.map (homOfLE n.le_succ).op =
            TypeCat.ofHom (((F.map (homOfLE n.le_succ).op).f 0).val.app V) from rfl]
          change ((quotientZeroIso l L Y F u n).hom.val.app V)
            (((F.map (homOfLE n.le_succ).op).f 0).val.app V x) = _
          rw [show G.map (homOfLE n.le_succ).op =
              TypeCat.ofHom ((integralCoefficientSheafTransition l L Y n).hom.app V) by
            simp only [G, integralCoefficientSheafSystem, Functor.comp_map,
              Functor.ofOpSequence_map_homOfLE_succ]
            rfl]
          exact ht n V.unop x)
    have ha (n : ℕᵒᵖ) : IsIso (a.app n) := by
      apply (bijective_iff_isIso_ofHom _).mp
      exact ConcreteCategory.bijective_of_isIso
        ((SheafOfModules.evaluation _ V).mapIso
          (quotientZeroIso l L Y F u n.unop)).hom
    have : IsIso a := NatIso.isIso_of_isIso_app a
    let hG := isLimitOfPreserves
      (sheafToPresheaf (Scheme.ProEt.topology Y) RingCat ⋙
        (evaluation Y.ProEtᵒᵖ RingCat).obj V ⋙ CategoryTheory.forget RingCat)
      (limit.isLimit (integralCoefficientSheafSystem l L Y))
    apply (IsLimit.postcomposeHomEquiv (asIso a) _).toFun
    refine IsLimit.ofIsoLimit hG (Cone.ext ?_ ?_)
    · with_unfolding_all
        exact ((SheafOfModules.evaluation _ V ⋙ CategoryTheory.forget _).mapIso
          (regularZeroIso l L Y)).symm
    · intro n
      ext s
      change ((limit.π (integralCoefficientSheafSystem l L Y) n).hom.app V) s =
        ((quotientZeroIso l L Y F u n.unop).hom.val.app V)
          (((g n.unop).f 0).val.app V (regularSection l L Y V.unop s))
      exact (hn n.unop V.unop s).symm
  · exact IsLimit.ofIsZero _
      (Functor.isZero _ (fun n ↦ hzero n.unop p hp))
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ p hp)

private theorem quotient_degreewise_epi
    (F : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l L Y) ℤ)
    (u : ∀ n : ℕ, F.obj (op n) ≅
      (integralOperationsRestrict l L Y n).obj (finiteRegularComplex l L Y n))
    (ht : ∀ (n : ℕ) (V : Y.ProEt) (x : ((F.obj (op (n + 1))).X 0).val.obj (op V)),
      ((quotientZeroIso l L Y F u n).hom.val.app (op V))
        (((F.map (homOfLE n.le_succ).op).f 0).val.app (op V) x) =
      (integralCoefficientSheafTransition l L Y n).hom.app (op V)
        (((quotientZeroIso l L Y F u (n + 1)).hom.val.app (op V)) x)) :
    ∀ (n : ℕ) (p : ℤ), Epi ((F.map (homOfLE n.le_succ).op).f p) := by
  intro n p
  by_cases hp : p = 0
  · subst p
    let T := SheafOfModules.toSheaf.{max u (t + 1)}
      (completedIntegralCoefficientSheafUnrestricted l L Y)
    let : HasSheafify (Scheme.ProEt.topology Y) AddCommGrpCat.{max u (t + 1)} :=
      integralCoefficientAbSheafify.{t, u} Y
    apply T.epi_of_epi_map
    suffices Sheaf.IsLocallySurjective (T.map ((F.map (homOfLE n.le_succ).op).f 0)) by
      let := this
      infer_instance
    constructor
    intro V x
    let a := quotientZeroIso l L Y F u n
    let b := quotientZeroIso l L Y F u (n + 1)
    have hr := transition_locallySurjective l L Y n
    refine (Scheme.ProEt.topology Y).superset_covering ?_
      (Presheaf.imageSieve_mem (Scheme.ProEt.topology Y)
        (integralCoefficientSheafTransition l L Y n).hom (a.hom.val.app (op V) x))
    rintro W f ⟨z, hz⟩
    refine ⟨b.inv.val.app (op W) z, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation _ (op W)).mapIso a).hom).1
    change a.hom.val.app (op W)
        (((F.map (homOfLE n.le_succ).op).f 0).val.app (op W)
          (b.inv.val.app (op W) z)) =
      a.hom.val.app (op W) (((F.obj (op n)).X 0).val.map f.op x)
    rw [ht]
    have hb : b.hom.val.app (op W) (b.inv.val.app (op W) z) = z := by
      change ((b.inv ≫ b.hom).val.app (op W)) z = z
      simp
    rw [hb, hz]
    exact (ConcreteCategory.congr_hom (a.hom.val.naturality f.op) x).symm
  · apply (IsZero.of_iso _
      ((HomologicalComplex.eval _ _ p).mapIso (u n))).epi
    exact (SheafOfModules.restrictScalars _).map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ p hp)

private theorem boundary_degreewise_epi
    (F : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l L Y) ℤ)
    (he : ∀ (n : ℕ) (p : ℤ),
      Epi ((F.map (homOfLE n.le_succ).op).f p)) :
    ∀ p : ℤ, Epi ((towerTransitionEndomorphism (K := fun n ↦ F.obj (op n))
      (integralOperationsTowerStep F)).f p) := by
  intro p
  let K := fun n : ℕ ↦ F.obj (op n)
  let ev := HomologicalComplex.eval (integralTowerModules l L Y) (.up ℤ) p
  let f := fun n : ℕ ↦ ev.map (F.map (homOfLE n.le_succ).op)
  let b := towerTransitionEndomorphism (K := K) (integralOperationsTowerStep F)
  change Epi (ev.map b)
  have hepi : Epi (towerTransitionEndomorphism (K := fun n ↦ ev.obj (K n)) f) := by
    obtain ⟨_, _, h, _⟩ := AlgebraicGeometry.ProEtale.proEtale_surjectiveTower_derivedLimit
      Y (completedIntegralCommRingSheafUnrestricted l L Y)
      (fun n ↦ ev.obj (K n)) f (fun n ↦ he n p)
    exact h
  let := hepi
  let e := PreservesProduct.iso ev K
  have hf : ev.map b ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism (K := fun n ↦ ev.obj (K n)) f := by
    apply Pi.hom_ext
    intro n
    simp only [e, PreservesProduct.iso_hom, Category.assoc, piComparison_comp_π]
    rw [← ev.map_comp, (towerTransitionEndomorphism_eq_iff _ _).mp rfl n,
      ev.map_sub, ev.map_comp,
      (towerTransitionEndomorphism_eq_iff _ _).mp rfl n]
    simp only [Preadditive.comp_sub]
    rw [← Category.assoc, piComparison_comp_π, piComparison_comp_π]
    rfl
  have : Epi (ev.map b ≫ e.hom) := by
    rw [hf]
    infer_instance
  exact (epi_comp_iff_of_isIso _ e.hom).mp inferInstance

private theorem tower_compatibility
    {B : Type*} [Category* B] (F : ℕᵒᵖ ⥤ B) {Z : B}
    (a : ∀ n : ℕ, Z ⟶ F.obj (Opposite.op n))
    (ha : ∀ n, a (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = a n)
    {n m : ℕ} (h : n ≤ m) : a m ≫ F.map (homOfLE h).op = a n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m h ih =>
    have he : (homOfLE (Nat.le_trans h (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    rw [he, F.map_comp, ← Category.assoc, ha, ih]

private theorem tower_kernel
    {B : Type*} [Category* B] [Preadditive B]
    (F : ℕᵒᵖ ⥤ B) (c : Cone F) (hc : IsLimit c)
    (P : Fan (fun n : ℕ ↦ F.obj (Opposite.op n))) (hP : IsLimit P)
    (i : c.pt ⟶ P.pt) (t : P.pt ⟶ P.pt)
    (hi : ∀ n : ℕ, i ≫ P.proj n = c.π.app (Opposite.op n))
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj n -
      P.proj (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) :
    ∃ h : i ≫ t = 0, Nonempty (IsLimit (KernelFork.ofι i h)) := by
  have hz : i ≫ t = 0 := by
    apply hP.hom_ext
    intro ⟨n⟩
    change (i ≫ t) ≫ P.proj n = 0 ≫ P.proj n
    rw [Category.assoc, ht, Preadditive.comp_sub, hi, ← Category.assoc, hi]
    simp only [zero_comp, sub_eq_zero]
    exact (c.w (homOfLE (Nat.le_succ n)).op).symm
  refine ⟨hz, ⟨Fork.IsLimit.mk' _ ?_⟩⟩
  intro s
  let Z := s.pt
  let k := s.ι
  have hk : k ≫ t = 0 := by
    have h := s.condition
    simp only [comp_zero] at h
    exact h
  have ha (n : ℕ) : (k ≫ P.proj (n + 1)) ≫
      F.map (homOfLE (Nat.le_succ n)).op = k ≫ P.proj n := by
    have hn := congrArg (fun f ↦ f ≫ P.proj n) hk
    rw [Category.assoc, ht, Preadditive.comp_sub, ← Category.assoc, zero_comp] at hn
    exact (sub_eq_zero.mp hn).symm
  let d : Cone F :=
    { pt := Z
      π := { app := fun n ↦ k ≫ P.proj n.unop
             naturality := by
               intro n m f
               change 𝟙 Z ≫ (k ≫ P.proj m.unop) =
                 (k ≫ P.proj n.unop) ≫ F.map f
               rw [Category.id_comp]
               symm
               exact tower_compatibility F (fun n ↦ k ≫ P.proj n) ha
                 (leOfHom f.unop) } }
  refine ⟨hc.lift d, ?_, ?_⟩
  · apply hP.hom_ext
    intro ⟨n⟩
    change (hc.lift d ≫ i) ≫ P.proj n = k ≫ P.proj n
    rw [Category.assoc, hi]
    exact hc.fac d (Opposite.op n)
  · intro l hl
    apply hc.hom_ext
    intro n
    change l ≫ i = k at hl
    calc
      l ≫ c.π.app n = k ≫ P.proj n.unop := by
        rw [← hi n.unop, ← Category.assoc, hl]
      _ = hc.lift d ≫ c.π.app n := (hc.fac d n).symm

private theorem kernel_cocone_quasiIso
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {P B : CochainComplex A ℤ} (f : B ⟶ B) (η : P ⟶ CochainComplex.mappingCocone f)
    (hz : (η ≫ CochainComplex.mappingCocone.fst f) ≫ f = 0)
    (hk : IsLimit (KernelFork.ofι (η ≫ CochainComplex.mappingCocone.fst f) hz))
    (he : ∀ p : ℤ, Epi (f.f p))
    (hs : ∀ p : ℤ, η.f p ≫
      (CochainComplex.mappingCocone.snd f).v p (p - 1) (by omega) = 0) :
    QuasiIso η := by
  obtain ⟨κ, hκ, hq, _⟩ :=
    CochainComplex.exists_kernel_to_shifted_mappingCone_of_degreewise_epi f he
  let e : P ≅ kernel f := hk.conePointUniqueUpToIso (limit.isLimit _)
  have hei : e.hom ≫ kernel.ι f = η ≫ CochainComplex.mappingCocone.fst f :=
    hk.conePointUniqueUpToIso_hom_comp (limit.isLimit _) WalkingParallelPair.zero
  have hη : η = e.hom ≫ κ := by
    apply HomologicalComplex.hom_ext
    intro p
    let eS := (CochainComplex.mappingCone f).shiftFunctorObjXIso (-1) p (p - 1)
      (by omega)
    apply (cancel_mono eS.hom).1
    apply HomologicalComplex.homotopyCofiber.ext_to_X f (p - 1) p
      (by change p - 1 + 1 = p; omega)
    · simp only [HomologicalComplex.comp_f]
      have hfst : (CochainComplex.mappingCocone.fst f).f p =
          ((CochainComplex.mappingCone f).shiftFunctorObjXIso (-1) p (p - 1)
            (by omega)).hom ≫
          HomologicalComplex.homotopyCofiber.fstX f (p - 1) p
            (by change p - 1 + 1 = p; omega) := by
        simp [CochainComplex.mappingCocone.fst, CochainComplex.mappingCone.fst,
          CochainComplex.shiftFunctorObjXIso,
          CochainComplex.HomComplex.Cochain.leftShift_v
            (n := 1) _ _ _ _ _ p _ (p - 1) (by omega)]
      have hh := congrArg (fun g ↦ g.f p) hei
      simp only [HomologicalComplex.comp_f] at hh
      dsimp only [eS]
      simp only [Category.assoc]
      rw [(hκ p).2]
      simpa only [hfst, Category.assoc] using hh.symm
    · simp only [HomologicalComplex.comp_f]
      have hsnd : (CochainComplex.mappingCocone.snd f).v p (p - 1) (by omega) =
          ((CochainComplex.mappingCone f).shiftFunctorObjXIso (-1) p (p - 1)
            (by omega)).hom ≫
          HomologicalComplex.homotopyCofiber.sndX f (p - 1) := by
        simp [CochainComplex.mappingCocone.snd, CochainComplex.mappingCone.snd,
          CochainComplex.shiftFunctorObjXIso,
          CochainComplex.HomComplex.Cochain.leftShift_v,
          Int.negOnePow_even 2 ⟨1, rfl⟩]
      dsimp only [eS]
      simp only [Category.assoc]
      rw [(hκ p).1, comp_zero]
      simpa only [hsnd, Category.assoc] using hs p
  rw [hη]
  infer_instance

private theorem projection_coordinates (n : ℕ) (V : Y.ProEt)
    (s : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj (op V)) :
    (((projectionComplex l L Y n).f 0 ≫
      (scalarReductionRestriction l L Y n).map (finiteZeroIso l L Y n).hom).val.app (op V))
      (regularSection l L Y V s) =
        (completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app (op V) s := by
  have h : (regularZeroIso l L Y).inv ≫ (projectionComplex l L Y n).f 0 ≫
      (scalarReductionRestriction l L Y n).map (finiteZeroIso l L Y n).hom =
        projectionModule l L Y n := by
    simp [projectionComplex, CochainComplex.singleFunctor,
      HomologicalComplex.single_map_f_self,
      Category.assoc, ← Functor.map_comp]
  change (((regularZeroIso l L Y).inv ≫ (projectionComplex l L Y n).f 0 ≫
    (scalarReductionRestriction l L Y n).map (finiteZeroIso l L Y n).hom).val.app (op V)) s = _
  rw [h]
  simp only [projectionModule, SheafOfModules.unitHomEquiv, PresheafOfModules.unitHomEquiv,
    LinearMap.ringLmapEquivSelf]
  change ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app (op V) s) * 1 = _
  exact mul_one _

private theorem tower_roos_triangle
    (F : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l L Y) ℤ)
    (c : Cone F) (hc : IsLimit c)
    (he : ∀ (n : ℕ) (p : ℤ), Epi ((F.map (homOfLE n.le_succ).op).f p)) :
    ∃ δ : DerivedCategory.Q.obj (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶
        (DerivedCategory.Q.obj c.pt)⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk
        (DerivedCategory.Q.map (Pi.lift (fun n : ℕ ↦ c.π.app (op n))))
        (DerivedCategory.Q.map (towerTransitionEndomorphism
          (K := fun n : ℕ ↦ F.obj (op n)) (integralOperationsTowerStep F))) δ ∈ distTriang _ := by
  let i := Pi.lift (fun n : ℕ ↦ c.π.app (op n))
  let b := towerTransitionEndomorphism
    (K := fun n : ℕ ↦ F.obj (op n)) (integralOperationsTowerStep F)
  obtain ⟨hz, ⟨hk⟩⟩ := tower_kernel F c hc _ (productIsProduct _)
    i b (by intro n; exact Pi.lift_comp_π _ n)
    ((towerTransitionEndomorphism_eq_iff _ _).mp rfl)
  have hm : Mono i := mono_of_isLimit_fork hk
  have hb : Epi b := HomologicalComplex.epi_of_epi_f b
    (boundary_degreewise_epi l L Y F he)
  let S := ShortComplex.mk i b hz
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (S.exact_of_f_is_kernel hk) hm hb
  exact ⟨DerivedCategory.triangleOfSESδ hS, DerivedCategory.triangleOfSES_distinguished hS⟩

private theorem localized_roos_triangle
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) [HasProduct (fun n : ℕ ↦ F.obj (op n))]
    (c : Cone F)
    (hp : IsLimit (Fan.mk (DerivedCategory.Q.obj (∏ᶜ fun n : ℕ ↦ F.obj (op n)))
      (fun n : ℕ ↦ DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦ F.obj (op n)) n))))
    (δ : DerivedCategory.Q.obj (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶
      (DerivedCategory.Q.obj c.pt)⟦(1 : ℤ)⟧)
    (hδ : Pretriangulated.Triangle.mk
      (DerivedCategory.Q.map (Pi.lift (fun n : ℕ ↦ c.π.app (op n))))
      (DerivedCategory.Q.map (towerTransitionEndomorphism
        (K := fun n : ℕ ↦ F.obj (op n)) (integralOperationsTowerStep F))) δ ∈ distTriang _) :
    ∃ hprod : HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj (op n))), letI := hprod
      ∃ δ' : (∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj (op n))) ⟶
        (DerivedCategory.Q.obj c.pt)⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle
          (fun n : ℕ ↦ DerivedCategory.Q.map (F.map (homOfLE n.le_succ).op))
          (DerivedCategory.Q.obj c.pt)
          (Pi.lift (fun n : ℕ ↦ DerivedCategory.Q.map (c.π.app (op n)))) δ' := by
  let Q := DerivedCategory.Q (C := A)
  let hprod : HasProduct (fun n : ℕ ↦ Q.obj (F.obj (op n))) := ⟨_, hp⟩
  let := hprod
  let e := hp.conePointUniqueUpToIso (productIsProduct _)
  have he (n : ℕ) : e.hom ≫ Pi.π _ n = Q.map (Pi.π (fun n : ℕ ↦ F.obj (op n)) n) :=
    hp.conePointUniqueUpToIso_hom_comp _ ⟨n⟩
  let b := towerTransitionEndomorphism
    (K := fun n : ℕ ↦ F.obj (op n)) (integralOperationsTowerStep F)
  have htrans : Q.map b ≫ e.hom = e.hom ≫ towerTransitionEndomorphism
      (K := fun n : ℕ ↦ Q.obj (F.obj (op n)))
      (fun n : ℕ ↦ Q.map (F.map (homOfLE n.le_succ).op)) := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, he]
    rw [← Q.map_comp, (towerTransitionEndomorphism_eq_iff _ _).mp rfl n,
      Q.map_sub, Q.map_comp,
      (towerTransitionEndomorphism_eq_iff _ _).mp rfl n]
    simp only [Preadditive.comp_sub, integralOperationsTowerStep]
    rw [← Category.assoc, he]
    rw [he]
  have hi : Q.map (Pi.lift (fun n : ℕ ↦ c.π.app (op n))) ≫ e.hom =
      Pi.lift (fun n : ℕ ↦ Q.map (c.π.app (op n))) := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, he, ← Q.map_comp, Pi.lift_comp_π]
    exact (Pi.lift_comp_π (fun n : ℕ ↦ Q.map (c.π.app (op n))) n).symm
  refine ⟨hprod, e.inv ≫ δ, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hδ _
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ ?_ ?_
  · dsimp only [Pretriangulated.Triangle.mk, Iso.refl_hom, Iso.symm_hom]
    rw [Category.id_comp]
    change Pi.lift _ ≫ e.inv = Q.map _
    rw [← hi, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · change towerTransitionEndomorphism _ ≫ e.inv = e.inv ≫ Q.map b
    apply (cancel_mono e.hom).1
    simpa [Category.assoc] using congrArg (fun x ↦ e.inv ≫ x) htrans.symm
  · change (e.inv ≫ δ) ≫ (𝟙 _)⟦(1 : ℤ)⟧' = e.inv ≫ δ
    simp

private theorem regular_complete
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p)
    (hg : integralOperationsGoodComplex l E Y (regularComplex l E Y))
    (hv : reductionUnits l E Y) :
    IsDerivedComplete l E Y D hl (DerivedCategory.Q.obj (regularComplex l E Y)) := by
  classical
  choose v hv₁ hv₂ hv₃ using hv
  let P := regularComplex l E Y
  let F : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E Y) ℤ :=
    Functor.ofOpSequence (X := fun n ↦ unrestrictedTowerComplex l E Y n P)
      (fun n ↦ unrestrictedTowerTransition l E Y P n)
  let u (n : ℕ) :=
    ((scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)).mapIso (v n)
  let g (n : ℕ) := unrestrictedTowerUnit l E Y P n
  have hn (n : ℕ) (V : Y.ProEt)
      (s : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V)) :
      ((quotientZeroIso l E Y F u n).hom.val.app (op V))
        (((g n).f 0).val.app (op V) (regularSection l E Y V s)) =
      (completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app (op V) s := by
    have h := congrArg (fun f ↦ f.f 0) (hv₂ n)
    have h' := congrArg (fun f ↦ f ≫
      (scalarReductionRestriction l E Y n).map (finiteZeroIso l E Y n).hom) h
    have h'' := congrArg (fun f ↦ f.val.app (op V) (regularSection l E Y V s)) h'
    exact h''.trans (projection_coordinates l E Y n V s)
  have ht (n : ℕ) (V : Y.ProEt)
      (x : ((F.obj (op (n + 1))).X 0).val.obj (op V)) :
      ((quotientZeroIso l E Y F u n).hom.val.app (op V))
        (((F.map (homOfLE n.le_succ).op).f 0).val.app (op V) x) =
      (integralCoefficientSheafTransition l E Y n).hom.app (op V)
        (((quotientZeroIso l E Y F u (n + 1)).hom.val.app (op V)) x) := by
    let a := quotientZeroIso l E Y F u n
    let b := quotientZeroIso l E Y F u (n + 1)
    let z : (integralCoefficientCommRingSheaf l E Y (n + 1)).obj.obj (op V) :=
      b.hom.val.app (op V) x
    have hx : b.inv.val.app (op V) z = x := by
      change ((b.hom ≫ b.inv).val.app (op V)) x = x
      simp only [Iso.hom_inv_id]
      rfl
    rw [← hx]
    rw [show F.map (homOfLE n.le_succ).op = unrestrictedTowerTransition l E Y P n from
      Functor.ofOpSequence_map_homOfLE_succ _ n]
    change a.hom.val.app (op V)
      (((unrestrictedTowerTransition l E Y P n).f 0).val.app (op V)
        (b.inv.val.app (op V) z)) = _
    have hb := hv₁ (n + 1) V z
    change b.inv.val.app (op V) z = _ at hb
    rw [hb]
    have hs := (unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose_spec
      P 0 (op V) z (regularSection l E Y V 1)
    change ((unrestrictedTowerTransition l E Y P n).f 0).val.app (op V)
      (unrestrictedTowerTensorSection l E Y (n + 1) (P.X 0) (op V) z
        (regularSection l E Y V 1)) =
      unrestrictedTowerTensorSection l E Y n (P.X 0) (op V)
        ((integralCoefficientSheafTransition l E Y n).hom.app (op V) z)
        (regularSection l E Y V 1) at hs
    rw [hs, ← hb]
    rw [← hv₁ n V]
    change ((a.inv ≫ a.hom).val.app (op V)) _ =
      (integralCoefficientSheafTransition l E Y n).hom.app (op V)
        (((b.inv ≫ b.hom).val.app (op V)) z)
    simp
  obtain ⟨π, hπ, ⟨hc⟩⟩ := quotient_ordinary_limit l E Y F u g hn ht
  have he := quotient_degreewise_epi l E Y F u ht
  obtain ⟨δ, hδ⟩ := tower_roos_triangle l E Y F (Cone.mk _ π) hc he
  have : CountableAB4Star (integralTowerModules l E Y) := countable_exact l E Y
  obtain ⟨hp⟩ := derivedCategory_termwiseProduct_isLimit (integralTowerModules l E Y)
    ℕ (fun n ↦ F.obj (op n))
  have hp' := (Fan.isLimitMapConeEquiv DerivedCategory.Q _ _) hp
  obtain ⟨hprod, δ', hδ'⟩ := localized_roos_triangle F (Cone.mk _ π) hp' δ hδ
  have hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) (𝟙 P) :=
    ⟨inferInstance, hg.1⟩
  refine ⟨P, P, 𝟙 P, hq, Iso.refl _, ?_⟩
  have hcond : integralTowerUnitCondition l E Y D hl P
      (unrestrictedTowerUnit l E Y P) ∧
      integralTowerTransitionCondition l E Y D hl P
        (unrestrictedTowerTransition l E Y P) := by
    constructor
    · exact unrestrictedTowerUnit_condition l E Y P
    · intro n i U s x
      have h := (unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose_spec
        P i U s x
      unfold unrestrictedIntegralTensorSection at h
      unfold unrestrictedTowerTransition unrestrictedIntegralTransition integralTowerTensorSection
      exact h
  have hm := (integralTowerMaps_existUnique l E Y D hl P).unique
    (integralTowerMaps_existUnique l E Y D hl P).exists.choose_spec
    (y₂ := (unrestrictedTowerUnit l E Y P, unrestrictedTowerTransition l E Y P)) hcond
  have hunit (n : ℕ) : integralTowerUnit l E Y D hl P n =
      unrestrictedTowerUnit l E Y P n := congrArg (fun a ↦ a.1 n) hm
  have hstep (n : ℕ) : integralTowerTransition l E Y D hl P n =
      unrestrictedTowerTransition l E Y P n := congrArg (fun a ↦ a.2 n) hm
  have htower (n : ℕ) :
      (integralReductionTower l E Y D hl P).map (homOfLE n.le_succ).op =
        DerivedCategory.Q.map (F.map (homOfLE n.le_succ).op) := by
    simp only [integralReductionTower, F, Functor.ofOpSequence_map_homOfLE_succ, hstep]
  have hlegs (n : ℕ) :
      (((integralReductionTowerCone l E Y D hl (𝟙 P) hq).extend
        (Iso.refl (DerivedCategory.Q.obj P)).inv).π.app (op n)) =
      DerivedCategory.Q.map (π.app (op n)) := by
    simp [integralReductionTowerCone, integralReductionTowerMap,
      integralTowerAugmentationIso, hunit, hπ, g]
  refine ⟨hprod, δ', ?_⟩
  change IsDerivedLimitTriangle
    (K := fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj (op n)))
    (fun n : ℕ ↦ (integralReductionTower l E Y D hl P).map (homOfLE n.le_succ).op)
    (DerivedCategory.Q.obj P)
    (Pi.lift (fun n ↦ (((integralReductionTowerCone l E Y D hl (𝟙 P) hq).extend
      (Iso.refl (DerivedCategory.Q.obj P)).inv).π.app (op n)))) δ'
  simpa only [htower, hlegs] using hδ'

-- Assemble the tower comparisons without unfolding the coefficient existence witnesses.
/-- The normalized unit is a quasi-isomorphism, with its ordinary-limit, derived-product,
Roos-triangle and inverse-projection identifications; the self-extension is complete.
Source: Bhatt--Scholze, Propositions 3.1.10 (p.17), 3.2.3(1) (p.18), 4.2.8 (p.29),
Definition 3.5.2 (p.24), Lemma 6.8.2(1) (pp.58--59)
(blueprint: lem-weil-constant-scalar-unit-quasi-isomorphism).

Proof:
1. lem-weil-l-adic-extension-integers-dvr and lem-weil-valued-dvr-finite-quotients
make every positive target quotient finite and its reductions surjective, also in
ramified extensions.
2. def-weil-pbc-constant-sheaf, lem-pe-ring-sheafification-underlying-sets and
lem-weil-pbc-site-sheafification-sections-local lift quotient sections locally.
The reductions are therefore locally surjective, i.e. epimorphisms of sheaves; the
sheafified sectionwise cokernel is zero, so they are epimorphic in modules
(situation-conventions).
3. The multiplication isomorphisms of lem-weil-constant-scalar-strict-unit identify
the strict tower with the target quotient tower. By
situation-conventions its ordinary limit is R_L[0],
with exactly the quotient legs (def-weil-completed-integral-coefficients).
4. lem-weil-proetale-surjective-tower-derived-limit gives that 1-s is degreewise epi
and its kernel inclusion is the ordinary limit inclusion. Outside degree zero all
terms vanish.
5. lem-weil-degreewise-epi-kernel-cocone-qis gives a quasi-isomorphism from this
kernel with unshifted component the inclusion and shifted component zero.
Uniqueness in lem-weil-constant-scalar-strict-unit identifies it with eta.
6. The same surjective-tower theorem identifies the actual termwise product as a
derived product and supplies the distinguished triangle with these very first and
second arrows, hence the Roos triangle of def-weil-derived-limit.
7. def-weil-abstract-derived-category inverts eta. For j_n = fst followed by pr_n,
the strict normalization says eta followed by j_n is the prescribed quotient leg.
Compose its localized equality with the inverse of Q(eta) to obtain the displayed
projection compatibility. The strict cone is precisely the representative used by
def-weil-integral-scalar-extension on the regular K-flat complex.
8. For the identity extension, the strict-unit reductionUnits assertion identifies
the first map with the canonical derived reduction units. The triangle therefore
proves def-weil-derived-complete. All arguments allow arbitrary Y, including the
empty scheme and disconnected schemes, and require no finiteness of Y.
-/
theorem regular_scalar_unit_quasi_isomorphism (D : FiniteFieldDatum.{d}) (_hl : l ≠ D.p)
    (η : regularComplex l L Y ⟶
      (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y))
    (_hη : quotientCoordinates l E Y L ι η ∧ zeroSecondComponent l E Y L ι η) :
    (∀ n : ℕ, Finite (Padic.coefficientExtensionRing l L (n + 1))) ∧
    (∀ n : ℕ, Sheaf.IsLocallySurjective (integralCoefficientSheafTransition l L Y n)) ∧
    (∃ e : regularComplex l L Y ≅ limit (tower l E L ι Y),
      ∀ n : ℕ, e.hom ≫ limit.π (tower l E L ι Y) (op n) = leg l E L ι Y η n) ∧
    QuasiIso η ∧
    Nonempty (IsLimit (Fan.mk (DerivedCategory.Q.obj (product l E L ι Y))
      (fun n : ℕ ↦ DerivedCategory.Q.map
        (Pi.π (fun m : ℕ ↦ (tower l E L ι Y).obj (op m)) n)))) ∧
    (∃ δ : DerivedCategory.Q.obj (product l E L ι Y) ⟶
        (DerivedCategory.Q.obj (regularComplex l L Y))⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk (DerivedCategory.Q.map (inclusion l E L ι Y η))
        (DerivedCategory.Q.map (boundary l E Y L ι)) δ ∈
          distTriang (DerivedCategory (integralTowerModules l L Y))) ∧
    (∃ e : DerivedCategory.Q.obj
        ((integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y)) ≅
          DerivedCategory.Q.obj (regularComplex l L Y),
      e.inv = DerivedCategory.Q.map η ∧
      ∀ n : ℕ, e.hom ≫ DerivedCategory.Q.map (leg l E L ι Y η n) =
        DerivedCategory.Q.map
          (CochainComplex.mappingCocone.fst (boundary l E Y L ι) ≫
            Pi.π (fun m : ℕ ↦ (tower l E L ι Y).obj (op m)) n)) ∧
    IntegralOnSlice.IsComplete l E Y none
      (DerivedCategory.Q.obj (regularComplex l E Y)) := by
  classical
  have hfinite (n : ℕ) := Padic.finite_coefficientExtensionRing l L (n + 1) (by omega)
  have hlocal := transition_locallySurjective l L Y
  have : CountableAB4Star (integralTowerModules l L Y) := countable_exact l L Y
  have hp : Nonempty (IsLimit (Fan.mk (DerivedCategory.Q.obj (product l E L ι Y))
      (fun n : ℕ ↦ DerivedCategory.Q.map
        (Pi.π (fun m : ℕ ↦ (tower l E L ι Y).obj (op m)) n)))) := by
    exact ⟨(Fan.isLimitMapConeEquiv DerivedCategory.Q _ _)
      ((derivedCategory_termwiseProduct_isLimit (integralTowerModules l L Y) ℕ
        (fun n ↦ (tower l E L ι Y).obj (op n))).some)⟩
  have hstrict := regular_scalar_strict_unit l E Y L ι D _hl
  have hgood := hstrict.1
  have hm := hstrict.2.1
  have hr := hstrict.2.2.2.1
  obtain ⟨u, _, hu, ht₀⟩ := hm
  let F := tower l E L ι Y
  let v (n : ℕ) := (integralOperationsRestrict l L Y n).mapIso (u n)
  have hn := normalized_coordinates l E L ι Y u hu η _hη.1
  have hstep (n : ℕ) : F.map (homOfLE n.le_succ).op =
      (integralScalarTransition l E L ι Y n).app (regularComplex l E Y) := by
    change ((Functor.ofOpSequence (X := fun n ↦ integralScalarLevel l E L ι Y n)
      (integralScalarTransition l E L ι Y)).map (homOfLE n.le_succ).op).app _ = _
    rw [Functor.ofOpSequence_map_homOfLE_succ]
  have ht₁ (n : ℕ) (V : Y.ProEt)
      (x : ((F.obj (op (n + 1))).X 0).val.obj (op V)) :
      ((quotientZeroIso l L Y F v n).hom.val.app (op V))
        (((F.map (homOfLE n.le_succ).op).f 0).val.app (op V) x) =
      (integralCoefficientSheafTransition l L Y n).hom.app (op V)
        (((quotientZeroIso l L Y F v (n + 1)).hom.val.app (op V)) x) := by
    rw [hstep]
    exact ht₀ n V x
  obtain ⟨π, hπ, ⟨hc⟩⟩ :=
    quotient_ordinary_limit l L Y F v (leg l E L ι Y η) hn ht₁
  have he := quotient_degreewise_epi l L Y F v ht₁
  let i := Pi.lift (fun n : ℕ ↦ π.app (op n))
  let b := towerTransitionEndomorphism
    (K := fun n : ℕ ↦ F.obj (op n)) (integralOperationsTowerStep F)
  obtain ⟨hz, ⟨hk⟩⟩ := tower_kernel
    (B := CochainComplex (integralTowerModules l L Y) ℤ) F (Cone.mk _ π) hc
    (Fan.mk (product l E L ι Y) (Pi.π (fun n : ℕ ↦ F.obj (op n))))
    (productIsProduct _) i b (by intro n; exact Pi.lift_comp_π _ n)
    ((towerTransitionEndomorphism_eq_iff _ _).mp rfl)
  have hei : i = inclusion l E L ι Y η := by
    apply Pi.hom_ext
    intro n
    exact (Pi.lift_comp_π _ n).trans (hπ n)
  have hb : b = boundary l E Y L ι := rfl
  have hz' : inclusion l E L ι Y η ≫ boundary l E Y L ι = 0 := by
    rw [← hei, ← hb]
    exact hz
  have hk' : IsLimit (KernelFork.ofι (inclusion l E L ι Y η) hz') := by
    simpa only [hei, hb] using hk
  have hq : QuasiIso η := kernel_cocone_quasiIso (boundary l E Y L ι) η hz' hk'
    (boundary_degreewise_epi l L Y F he) _hη.2
  have hi : ∃ e : DerivedCategory.Q.obj
      ((integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y)) ≅
        DerivedCategory.Q.obj (regularComplex l L Y),
      e.inv = DerivedCategory.Q.map η ∧
      ∀ n : ℕ, e.hom ≫ DerivedCategory.Q.map (leg l E L ι Y η n) =
        DerivedCategory.Q.map
          (CochainComplex.mappingCocone.fst (boundary l E Y L ι) ≫
            Pi.π (fun m : ℕ ↦ (tower l E L ι Y).obj (op m)) n) := by
    refine ⟨(asIso (DerivedCategory.Q.map η)).symm, rfl, ?_⟩
    intro n
    simp only [Iso.symm_hom, asIso_inv, leg, inclusion, Functor.map_comp,
      ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have ht : ∃ δ : DerivedCategory.Q.obj (product l E L ι Y) ⟶
      (DerivedCategory.Q.obj (regularComplex l L Y))⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk (DerivedCategory.Q.map (inclusion l E L ι Y η))
        (DerivedCategory.Q.map (boundary l E Y L ι)) δ ∈ distTriang _ := by
    let Q := DerivedCategory.Q (C := integralTowerModules l L Y)
    let T := Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle (boundary l E Y L ι))
    have hT : T ∈ distTriang _ :=
      DerivedCategory.mappingCocone_triangle_distinguished _
    let δ := T.mor₃ ≫ (inv (Q.map η))⟦(1 : ℤ)⟧'
    refine ⟨δ, ?_⟩
    apply Pretriangulated.isomorphic_distinguished T hT
    refine Pretriangulated.Triangle.isoMk _ _ (asIso (Q.map η))
      (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · change Q.map (inclusion l E L ι Y η) ≫ 𝟙 _ =
        Q.map η ≫ Q.map (CochainComplex.mappingCocone.fst (boundary l E Y L ι))
      simp only [inclusion, Functor.map_comp, Category.comp_id]
    · change Q.map (boundary l E Y L ι) ≫ 𝟙 _ = 𝟙 _ ≫ Q.map (boundary l E Y L ι)
      simp
    · dsimp only [Pretriangulated.Triangle.mk, Iso.refl_hom, asIso_hom]
      simp [δ]
  refine ⟨hfinite, hlocal, ?_, hq, hp, ht, hi, ?_⟩
  · refine ⟨hc.conePointUniqueUpToIso (limit.isLimit F), ?_⟩
    intro n
    exact (hc.conePointUniqueUpToIso_hom_comp (limit.isLimit F) (op n)).trans (hπ n)
  · obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    let : Fact p.Prime := ⟨hprime⟩
    let D₀ : FiniteFieldDatum.{0} :=
      { p := p
        a := 1
        q := p
        prime := hprime
        exponent_pos := by decide
        cardinality_eq := by simp
        k₀ := ZMod p
        card_base := by simp [Nat.card_eq_fintype_card]
        k := AlgebraicClosure (ZMod p) }
    have hl₀ : l ≠ D₀.p := by change l ≠ p; omega
    exact ⟨D₀, hl₀, regular_complete l E Y D₀ hl₀ hgood hr⟩

end WeilConjectures.ConstantScalarUnitQuasiIsomorphism
