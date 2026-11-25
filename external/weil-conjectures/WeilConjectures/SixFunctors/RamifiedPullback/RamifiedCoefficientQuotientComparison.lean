/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedPullbackTowerData
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedCoefficientRegularQuotients
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison

/-! # Ramified coefficient quotient comparison

Source: Stacks 093M, 03EK and 03EL; Bhatt--Scholze 6.8.2(1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.RamifiedPullback

section QuotientBaseChange
universe a b r
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S A B : Sheaf J CommRingCat.{r}}

private abbrev underlyingRing (R : Sheaf J CommRingCat.{r}) :=
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R

private abbrev quotientModule (p : R ⟶ A) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map p)).obj
      (SheafOfModules.unit (underlyingRing A))

private abbrev quotientSections (p : R ⟶ A) (U : Cᵒᵖ) : ModuleCat (R.obj.obj U) :=
  (ModuleCat.restrictScalars (p.hom.app U).hom).obj
    (ModuleCat.of (A.obj.obj U) (A.obj.obj U))

private def quotientSectionMap (c : R ⟶ S) (p : R ⟶ A) (q : S ⟶ B)
    (j : A ⟶ B) (h : p ≫ j = c ≫ q) (U : Cᵒᵖ) :
    (ModuleCat.extendScalars (c.hom.app U).hom).obj (quotientSections p U) ⟶
      quotientSections q U :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (c.hom.app U).hom
    (ModuleCat.ofHom
      (X := quotientSections p U)
      (Y := (ModuleCat.restrictScalars (c.hom.app U).hom).obj
        (quotientSections q U))
      { toFun := j.hom.app U
        map_add' := map_add _
        map_smul' := fun x y ↦ by
          change j.hom.app U (p.hom.app U x * (show A.obj.obj U from y)) =
            q.hom.app U (c.hom.app U x) * j.hom.app U y
          rw [map_mul]
          exact congrArg (fun z ↦ z * j.hom.app U y)
            (congrArg (fun f ↦ f.hom.app U x) h) })

omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}] in
private theorem quotientSectionMap_tmul (c : R ⟶ S) (p : R ⟶ A) (q : S ⟶ B)
    (j : A ⟶ B) (h : p ≫ j = c ≫ q) (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : quotientSections p U) :
    quotientSectionMap c p q j h U (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x) =
      q.hom.app U s * j.hom.app U x := by
  let : Module (R.obj.obj U) (S.obj.obj U) :=
    Module.compHom (S.obj.obj U) (c.hom.app U).hom
  let : Module (R.obj.obj U) (quotientSections q U) :=
    Module.compHom (quotientSections q U) (c.hom.app U).hom
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}] in
private theorem quotientSectionMap_bijective (c : R ⟶ S) (p : R ⟶ A) (q : S ⟶ B)
    (j : A ⟶ B) (h : p ≫ j = c ≫ q) (U : Cᵒᵖ)
    (hp : Function.Surjective (p.hom.app U))
    (hq : Function.Surjective (q.hom.app U))
    (hk : RingHom.ker (q.hom.app U).hom =
      Ideal.map (c.hom.app U).hom (RingHom.ker (p.hom.app U).hom)) :
    Function.Bijective (quotientSectionMap c p q j h U) := by
  let : Module (R.obj.obj U) (S.obj.obj U) :=
    Module.compHom (S.obj.obj U) (c.hom.app U).hom
  let : Module (R.obj.obj U) (A.obj.obj U) :=
    Module.compHom (A.obj.obj U) (p.hom.app U).hom
  let T := (ModuleCat.extendScalars (c.hom.app U).hom).obj (quotientSections p U)
  let v : S.obj.obj U →ₗ[S.obj.obj U] T :=
    (LinearMap.id : S.obj.obj U →ₗ[S.obj.obj U] S.obj.obj U).smulRight
      ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.app U).hom]
        ((1 : A.obj.obj U) : quotientSections p U))
  have hv (s : S.obj.obj U) : v s =
      s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] ((1 : A.obj.obj U) : quotientSections p U) := by
    change (s * 1) ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] ((1 : A.obj.obj U) : quotientSections p U) = _
    rw [mul_one]
  have hvp (x : R.obj.obj U) : v (c.hom.app U x) =
      (1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.app U).hom]
        (show quotientSections p U from p.hom.app U x) := by
    rw [hv]
    have hh := TensorProduct.smul_tmul (R := R.obj.obj U) x (1 : S.obj.obj U)
      ((1 : A.obj.obj U) : quotientSections p U)
    change (c.hom.app U x * 1) ⊗ₜ[R.obj.obj U]
        ((1 : A.obj.obj U) : quotientSections p U) =
      (1 : S.obj.obj U) ⊗ₜ[R.obj.obj U]
        (show quotientSections p U from p.hom.app U x * 1) at hh
    simpa only [mul_one] using hh
  have hkill : Ideal.map (c.hom.app U).hom (RingHom.ker (p.hom.app U).hom) ≤
      LinearMap.ker v := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change v (c.hom.app U x) = 0
    rw [hvp, show p.hom.app U x = 0 from hx, TensorProduct.tmul_zero]
  have hgen (z : T) : ∃ s, v s = z := by
    induction z using TensorProduct.inductionOn with
    | tmul s x =>
      obtain ⟨x, rfl⟩ := hp x
      refine ⟨(show S.obj.obj U from s) * c.hom.app U x, ?_⟩
      rw [← smul_eq_mul, map_smul, hvp]
      change ((show S.obj.obj U from s) * 1) ⊗ₜ[R.obj.obj U] _ = _
      rw [mul_one]
    | add x y hx hy =>
      obtain ⟨s, rfl⟩ := hx
      obtain ⟨t, rfl⟩ := hy
      exact ⟨s + t, map_add v s t⟩
  constructor
  · apply (quotientSectionMap c p q j h U).hom.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro z hz
    change z = 0
    obtain ⟨s, rfl⟩ := hgen z
    have hs : q.hom.app U s = 0 := by
      change quotientSectionMap c p q j h U (v s) = 0 at hz
      rw [hv] at hz
      erw [quotientSectionMap_tmul, map_one, mul_one] at hz
      exact hz
    apply hkill
    rw [← hk]
    exact hs
  · intro z
    obtain ⟨s, rfl⟩ := hq z
    refine ⟨v s, ?_⟩
    rw [hv, quotientSectionMap_tmul, map_one, mul_one]

private theorem quotientBaseChange (c : R ⟶ S) (p : R ⟶ A) (q : S ⟶ B)
    (j : A ⟶ B) (h : p ≫ j = c ≫ q)
    (hp : ∀ U, Function.Surjective (p.hom.app U))
    (hq : ∀ U, Function.Surjective (q.hom.app U))
    (hk : ∀ U, RingHom.ker (q.hom.app U).hom =
      Ideal.map (c.hom.app U).hom (RingHom.ker (p.hom.app U).hom)) :
    ∃ e : SheafOfModules.changeOfRings c (quotientModule p) ≅ quotientModule q,
      ∀ U s x, e.hom.val.app U
        ((toSheafify J
          (SheafOfModules.changeOfRingsPresheaf c (quotientModule p)).presheaf).app U
            (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x)) =
              q.hom.app U s * j.hom.app U x := by
  let f : SheafOfModules.changeOfRingsPresheaf c (quotientModule p) ⟶
      (quotientModule q).val :=
    { app := quotientSectionMap c p q j h
      naturality := by
        intro U V i
        apply ModuleCat.ExtendScalars.hom_ext
        intro x
        change quotientSectionMap c p q j h V
          ((SheafOfModules.changeOfRingsPresheaf c (quotientModule p)).map i
            ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x)) = _
        rw [show (SheafOfModules.changeOfRingsPresheaf c (quotientModule p)).map i
            ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x) = _ from
            Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap c
              (quotientModule p) i) 1 x, map_one,
          quotientSectionMap_tmul, map_one, one_mul]
        change j.hom.app V (A.obj.map i x) =
          B.obj.map i (quotientSectionMap c p q j h U
            ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x))
        rw [quotientSectionMap_tmul, map_one, one_mul]
        exact ConcreteCategory.congr_hom (j.hom.naturality i) x }
  let eP : SheafOfModules.changeOfRingsPresheaf c (quotientModule p) ≅
      (quotientModule q).val := PresheafOfModules.isoMk (fun U ↦
    (LinearEquiv.ofBijective (f.app U).hom
      (quotientSectionMap_bijective c p q j h U (hp U) (hq U) (hk U))).toModuleIso)
    (by intro U V i; exact f.naturality i)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (underlyingRing S).obj)
  let e := (PresheafOfModules.sheafification (𝟙 (underlyingRing S).obj)).mapIso eP ≪≫
    (asIso adj.counit).app (quotientModule q)
  refine ⟨e, ?_⟩
  intro U s x
  have hn := congrArg (fun a ↦ a.app U
    (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x)) (adj.unit.naturality eP.hom)
  have hc := congrArg (fun a ↦ a.app U (f.app U
    (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x)))
      (adj.right_triangle_components (quotientModule q))
  exact (congrArg ((adj.counit.app (quotientModule q)).val.app U) hn.symm).trans
    (hc.trans (quotientSectionMap_tmul c p q j h U s x))

end QuotientBaseChange

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private def residueRings : ℕᵒᵖ ⥤ CommRingCat.{max u (t + 1)} where
  obj n := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n.unop + 1)))
  map f := CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((Ideal.Quotient.factorPow (Ideal.span {Padic.coefficientExtensionUniformizer l E})
      (Nat.add_le_add_right (leOfHom f.unop) 1)).comp ULift.ringEquiv.toRingHom))
  map_id n := by
    ext x
    rcases x with ⟨x⟩
    induction x using Quotient.inductionOn with
    | h x => rfl
  map_comp f g := by
    ext x
    rcases x with ⟨x⟩
    induction x using Quotient.inductionOn with
    | h x => rfl

private def residueDiagram (W : Scheme.{t}) :=
  residueRings.{t, u} l E ⋙ constantSheaf (Scheme.ProEt.topology W)
    CommRingCat.{max u (t + 1)}

private theorem residueDiagram_map (W : Scheme.{t}) (a b : ℕ) (h : a ≤ b) :
    (integralCoefficientSheafSystem l E W).map (homOfLE h).op =
      (sheafCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        ((residueDiagram l E W).map (homOfLE h).op) := by
  let α : integralCoefficientSheafSystem l E W ⟶ residueDiagram l E W ⋙
      sheafCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}) :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ, Functor.comp_map,
        Category.comp_id, Category.id_comp]
      rfl)
  exact (Category.comp_id _).symm.trans ((α.naturality (homOfLE h).op).trans
    (Category.id_comp _))

private theorem projection_reduction (W : Scheme.{t}) (a b : ℕ) (h : a ≤ b) :
    completedIntegralCommRingProjectionUnrestricted l E W b ≫
      (residueDiagram l E W).map (homOfLE h).op =
        completedIntegralCommRingProjectionUnrestricted l E W a := by
  apply (sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map_injective
  rw [Functor.map_comp, ← residueDiagram_map]
  exact limit.w (integralCoefficientSheafSystem l E W) (homOfLE h).op

private theorem ramified_transition (e : ℕ)
    (j : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1))
    (hj : ∀ (n : ℕ) (a : Padic.coefficientExtensionIntegers l E),
      j n (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a) =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (index e n + 1))
          (integralScalarIntegerInclusion l E L ι a))
    (W : Scheme.{t}) (a b : ℕ) (h : a ≤ b) (h' : index e a ≤ index e b) :
    (residueDiagram l E W).map (homOfLE h).op ≫ ramifiedMap l E L W e a (j a) =
      ramifiedMap l E L W e b (j b) ≫
        (residueDiagram l L W).map (homOfLE h').op := by
  change constantMap W _ ≫ constantMap W _ = constantMap W _ ≫ constantMap W _
  unfold constantMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext x
  rcases x with ⟨x⟩
  induction x using Quotient.inductionOn with
  | h x =>
    change j a (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.factorPow _ (Nat.add_le_add_right h' 1)
        (j b (Ideal.Quotient.mk _ x))
    rw [hj, hj]
    rfl

private theorem ramified_projection (e : ℕ) (he : 1 ≤ e)
    (j : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1))
    (hj : ∀ (n : ℕ) (a : Padic.coefficientExtensionIntegers l E),
      j n (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a) =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (index e n + 1))
          (integralScalarIntegerInclusion l E L ι a)) (W : Scheme.{t}) (n : ℕ) :
    completedCoefficientMap l E L ι W ≫
        completedIntegralCommRingProjectionUnrestricted l L W (index e n) =
      completedIntegralCommRingProjectionUnrestricted l E W n ≫
        ramifiedMap l E L W e n (j n) := by
  have hn : n ≤ index e n := by
    dsimp [index]
    have hh := Nat.mul_le_mul_right (n + 1) he
    omega
  rw [completedCoefficientMap_projection]
  rw [← projection_reduction l E W n (index e n) hn, Category.assoc]
  congr 1
  change constantMap W _ = constantMap W _ ≫ constantMap W _
  unfold constantMap
  rw [← Functor.map_comp]
  congr 1
  ext x
  rcases x with ⟨x⟩
  induction x using Quotient.inductionOn with
  | h x =>
    change integralScalarQuotientMap l E L ι (index e n) (Ideal.Quotient.mk _ x) =
      j n (Ideal.Quotient.mk _ x)
    rw [hj]
    rfl

/-- Extension of a completed coefficient quotient is the quotient by the extended ideal.
Source: Stacks 093M and 03EK; the coefficient part of Bhatt--Scholze 6.8.2(1).
(blueprint: lem-weil-ramified-coefficient-quotient-comparison).

Proof: Define the completed map by the compatible same-index quotient inclusions.
Its ramified projection factors through the source quotient: the image of its
uniformizer ideal is the target uniformizer ideal to power e. The quotient maps on
representatives give precisely j. Both completed projections are locally surjective,
and their kernels are generated by the relevant uniformizer powers, by Stacks 093M.
Thus the target kernel is the extension of the source kernel. The balanced map
s tensor a to j(a) pi(s) is invertible: locally lift a to r and send a target residue
of s to s tensor 1. Changing a lift adds a multiple of the source uniformizer power;
balancing kills it, proving both inverse equations. These maps commute with
restriction and descend through sheafification. Reducing representatives proves
compatibility of j with every quotient transition; the limit equations give the
same compatibility for pi(s). Their product is the coefficient transition formula.
The construction uses only ideal equality and not a chosen relating unit. -/
theorem coefficients_exists (e : ℕ) (he : 1 ≤ e)
    (hideal : Ideal.span
      ({integralScalarIntegerInclusion l E L ι (Padic.coefficientExtensionUniformizer l E)} :
        Set (Padic.coefficientExtensionIntegers l L)) =
      Ideal.span {Padic.coefficientExtensionUniformizer l L ^ e})
    (hexp : ∀ n : ℕ, index e n + 1 = e * (n + 1))
    (j : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1))
    (hj : ∀ (n : ℕ) (a : Padic.coefficientExtensionIntegers l E),
      j n (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a) =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (index e n + 1))
          (integralScalarIntegerInclusion l E L ι a)) (W : Scheme.{t}) :
    Nonempty (Coefficients l E L ι e j W) := by
  classical
  let c := completedCoefficientMap l E L ι W
  have hram := ramified_projection l E L ι e he j hj W
  have hsurj (F : Type u) [Field F] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F] (n : ℕ) (U : W.ProEtᵒᵖ) :
      Function.Surjective
        ((completedIntegralCommRingProjectionUnrestricted l F W n).hom.app U) :=
    AlgebraicGeometry.ProEtale.projection_surjective l F W _
      (AlgebraicGeometry.ProEtale.uniformizer_normalized l F W n) U
  have hker (n : ℕ) (U : W.ProEtᵒᵖ) :
      RingHom.ker
        ((completedIntegralCommRingProjectionUnrestricted l L W (index e n)).hom.app U).hom =
      Ideal.map (c.hom.app U).hom
        (RingHom.ker
          ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U).hom) := by
    rw [AlgebraicGeometry.ProEtale.uniformizer_kernel,
      AlgebraicGeometry.ProEtale.uniformizer_kernel]
    change Ideal.span
        {scalarValue l L W U (Padic.coefficientExtensionUniformizer l L) ^ (index e n + 1)} =
      Ideal.map (c.hom.app U).hom
        (Ideal.span {scalarValue l E W U (Padic.coefficientExtensionUniformizer l E) ^ (n + 1)})
    rw [Ideal.map_span, Set.image_singleton, map_pow]
    have hc := scalarValue_map l E W L ι U (Padic.coefficientExtensionUniformizer l E)
    change (c.hom.app U).hom _ = _ at hc
    erw [hc]
    have hh := congrArg (fun I ↦ Ideal.map (scalarValue l L W U) (I ^ (n + 1))) hideal
    simp only [Ideal.map_span, Set.image_singleton, map_pow,
      Ideal.span_singleton_pow, ← pow_mul, hexp n] at hh ⊢
    convert! hh.symm using 1
  have hiso (n : ℕ) :
      ∃ d : (scalar c).obj (coefficientModule l E W n) ≅
          coefficientModule l L W (index e n),
        ∀ (U : W.ProEtᵒᵖ)
          (a : (integralCoefficientCommRingSheaf l E W n).obj.obj U)
          (s : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U),
          d.hom.val.app U (tensor c (coefficientModule l E W n) U s a) =
            (ramifiedMap l E L W e n (j n)).hom.app U a *
              (completedIntegralCommRingProjectionUnrestricted l L W (index e n)).hom.app U s := by
    obtain ⟨d, hd⟩ := quotientBaseChange c
      (completedIntegralCommRingProjectionUnrestricted l E W n)
      (completedIntegralCommRingProjectionUnrestricted l L W (index e n))
      (ramifiedMap l E L W e n (j n)) (hram n).symm
      (hsurj E n) (hsurj L (index e n)) (hker n)
    let hM := (scalarWitness c).choose_spec.choose (coefficientModule l E W n)
    refine ⟨eqToIso hM ≪≫ d, ?_⟩
    intro U a s
    change d.hom.val.app U
      (((eqToHom hM.symm ≫ eqToHom hM).val.app U)
        ((toSheafify (Scheme.ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf c (coefficientModule l E W n)).presheaf).app U
            (s ⊗ₜ[_, (c.hom.app U).hom] a))) = _
    rw [eqToHom_trans, eqToHom_refl]
    change d.hom.val.app U
      ((toSheafify (Scheme.ProEt.topology W)
        (SheafOfModules.changeOfRingsPresheaf c (coefficientModule l E W n)).presheaf).app U
          (s ⊗ₜ[_, (c.hom.app U).hom] a)) = _
    calc
      _ = (completedIntegralCommRingProjectionUnrestricted l L W (index e n)).hom.app U s *
          (ramifiedMap l E L W e n (j n)).hom.app U a := hd U s a
      _ = _ := mul_comm _ _
  choose d hd using hiso
  refine ⟨{ completedMap := c
            projection := (completedCoefficientMap_existsUnique l E L ι W).exists.choose_spec
            ramified_projection := hram
            coefficientIso := d
            coefficient_formula := hd
            coefficient_transitions := ?_ }⟩
  intro a b h h' U x s
  rw [hd, hd, map_mul]
  let F := sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  have ht : (integralCoefficientSheafSystem l E W).map (homOfLE h).op ≫
        F.map (ramifiedMap l E L W e a (j a)) =
      F.map (ramifiedMap l E L W e b (j b)) ≫
        (integralCoefficientSheafSystem l L W).map (homOfLE h').op := by
    rw [residueDiagram_map l E W, residueDiagram_map l L W]
    exact (F.map_comp _ _).symm.trans
      ((congrArg F.map (ramified_transition l E L ι e j hj W a b h h')).trans
        (F.map_comp _ _))
  have hjt := congrArg (fun f ↦ f.hom.app U x) ht
  have hpt := congrArg (fun f ↦ f.hom.app U s)
    (limit.w (integralCoefficientSheafSystem l L W) (homOfLE h').op)
  exact congrArg₂ (fun x y : (integralCoefficientCommRingSheaf l L W (index e a)).obj.obj U ↦
    x * y) hjt hpt.symm

end WeilConjectures.RamifiedPullback
