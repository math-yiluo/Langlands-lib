/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import WeilConjectures.CategoryTheory.SmoothPurity.AdicBasisLimit
import WeilConjectures.NumberTheory.Padics.LocalFieldIntegralBasis
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! # Finite freeness of the specified completed integral coefficient inclusion

The coefficient and site universes are independent. The coefficient map is fixed by its
finite reductions, so the transported basis has the specified scalar action.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-weil-completed-integral-finite-free).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
universe t u a b r
open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators
namespace WeilConjectures
section RingTransport
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  {R S : Sheaf J RingCat.{r}}
private noncomputable def restrictionRoundTrip (c : R ≅ S) :
    SheafOfModules.restrictScalars.{r} c.hom ⋙
      SheafOfModules.restrictScalars c.inv ≅ 𝟭 (SheafOfModules.{r} S) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget S).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (c.inv.hom.app U).hom
        (c.hom.hom.app U).hom (RingHom.id _) (by
          have h := congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) c.inv_hom_id) U
          exact (congrArg RingCat.Hom.hom h).symm) (M.val.obj U)).symm ≪≫
        ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.val.obj U))
      (by intro U V f; ext x; rfl)))
    (by intro M N f; ext U x; rfl)
private noncomputable def restrictionEquivalence (c : R ≅ S) :
    SheafOfModules.{r} S ≌ SheafOfModules.{r} R where
  functor := SheafOfModules.restrictScalars c.hom
  inverse := SheafOfModules.restrictScalars c.inv
  unitIso := (restrictionRoundTrip c).symm
  counitIso := restrictionRoundTrip c.symm
  functor_unitIso_comp M := by ext U x; rfl
private noncomputable def unitRestriction (c : R ≅ S) :
    SheafOfModules.unit R ≅
      (SheafOfModules.restrictScalars.{r} c.hom).obj (SheafOfModules.unit S) := by
  apply (SheafOfModules.fullyFaithfulForget R).preimageIso
  refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
  · exact (show (SheafOfModules.unit R).val.obj U ≃ₗ[R.obj.obj U]
        ((SheafOfModules.restrictScalars.{r} c.hom).obj
          (SheafOfModules.unit S)).val.obj U from
      { toFun := c.hom.hom.app U
        invFun := c.inv.hom.app U
        left_inv := fun x ↦ by
          exact ConcreteCategory.congr_hom (congr_app
            (congrArg (fun f : R ⟶ R ↦ f.hom) c.hom_inv_id) U) x
        right_inv := fun x ↦ by
          exact ConcreteCategory.congr_hom (congr_app
            (congrArg (fun f : S ⟶ S ↦ f.hom) c.inv_hom_id) U) x
        map_add' := map_add _
        map_smul' := fun r x ↦ by
          change R.obj.obj U at x
          exact (c.hom.hom.app U).hom.map_mul r x }).toModuleIso
  · intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (c.hom.hom.naturality f) x
private noncomputable def restrictionCompose {T : Sheaf J RingCat.{r}}
    (f : R ⟶ S) (g : S ⟶ T) :
    SheafOfModules.restrictScalars.{r} g ⋙ SheafOfModules.restrictScalars f ≅
      SheafOfModules.restrictScalars (f ≫ g) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (f.hom.app U).hom (g.hom.app U).hom
        ((f ≫ g).hom.app U).hom rfl (M.val.obj U)).symm)
      (by intro U V h; ext x; rfl)))
    (by intro M N h; ext U x; rfl)

private noncomputable def restrictedUnitIso {T : Sheaf J RingCat.{r}}
    (f : R ⟶ S) (g : R ⟶ T) (c : S ≅ T) (h : f ≫ c.hom = g) :
    (SheafOfModules.restrictScalars.{r} f).obj (SheafOfModules.unit S) ≅
      (SheafOfModules.restrictScalars g).obj (SheafOfModules.unit T) := by
  apply (SheafOfModules.fullyFaithfulForget R).preimageIso
  refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
  · exact (show ((SheafOfModules.restrictScalars.{r} f).obj
        (SheafOfModules.unit S)).val.obj U ≃ₗ[R.obj.obj U]
        ((SheafOfModules.restrictScalars.{r} g).obj
          (SheafOfModules.unit T)).val.obj U from
      { toFun := c.hom.hom.app U
        invFun := c.inv.hom.app U
        left_inv := fun x ↦ ConcreteCategory.congr_hom (congr_app
          (congrArg (fun f : S ⟶ S ↦ f.hom) c.hom_inv_id) U) x
        right_inv := fun x ↦ ConcreteCategory.congr_hom (congr_app
          (congrArg (fun f : T ⟶ T ↦ f.hom) c.inv_hom_id) U) x
        map_add' := map_add _
        map_smul' := fun r x ↦ by
          change S.obj.obj U at x
          change c.hom.hom.app U (f.hom.app U r * x) =
            g.hom.app U r * c.hom.hom.app U x
          rw [map_mul]
          exact congrArg (· * c.hom.hom.app U x)
            (ConcreteCategory.congr_hom (congr_app
              (congrArg (fun f : R ⟶ T ↦ f.hom) h) U) r) }).toModuleIso
  · intro U V h
    ext x
    exact ConcreteCategory.congr_hom (c.hom.hom.naturality h) x

private theorem freeTransport {R' S' : Sheaf J RingCat.{r}}
    (eR : R' ≅ R) (eS : S' ≅ S) (f : R' ⟶ S') (g : R ⟶ S)
    (h : f ≫ eS.hom = eR.hom ≫ g) (d : ℕ)
    (e : (SheafOfModules.restrictScalars.{r} f).obj (SheafOfModules.unit S') ≅
      ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit R') :
    Nonempty ((SheafOfModules.restrictScalars.{r} g).obj (SheafOfModules.unit S) ≅
      ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit R) := by
  let U := SheafOfModules.restrictScalars.{r} eR.inv
  let : U.IsEquivalence := (restrictionEquivalence eR.symm).isEquivalence_functor
  have h' : (eR.inv ≫ f) ≫ eS.hom = g := by
    rw [Category.assoc, h, ← Category.assoc, eR.inv_hom_id, Category.id_comp]
  let k := (restrictionCompose eR.inv f).app (SheafOfModules.unit S') ≪≫
    restrictedUnitIso (eR.inv ≫ f) g eS h'
  let n := unitRestriction eR.symm
  exact ⟨k.symm ≪≫ U.mapIso e ≪≫ PreservesProduct.iso U _ ≪≫
    Pi.mapIso (fun _ : Fin d ↦ n.symm)⟩

end RingTransport
section IntegralBasis
private noncomputable def liftedBasis {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] {d : ℕ} (b : Module.Basis (Fin d) A B) :
    let : Algebra (ULift.{t + 1} A) B := ULift.algebra' A B
    Module.Basis (Fin d) (ULift.{t + 1} A) (ULift.{t + 1} B) := by
  let : Algebra (ULift.{t + 1} A) B := ULift.algebra' A B
  apply Module.Basis.ofEquivFun
  exact
    { toFun := fun x i ↦ ULift.up (b.equivFun x.down i)
      invFun := fun c ↦ ULift.up (b.equivFun.symm (fun i ↦ (c i).down))
      left_inv := fun x ↦ by
        apply ULift.ext
        exact b.equivFun.symm_apply_apply x.down
      right_inv := fun c ↦ by
        funext i
        apply ULift.ext
        exact congrFun (b.equivFun.apply_symm_apply (fun i ↦ (c i).down)) i
      map_add' := fun x y ↦ by
        funext i
        apply ULift.ext
        exact congrFun (b.equivFun.map_add x.down y.down) i
      map_smul' := fun a x ↦ by
        funext i
        apply ULift.ext
        exact congrFun (b.equivFun.map_smul a.down x.down) i }

variable (l : ℕ) [Fact l.Prime] (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem integral_basis :
    let := ι.toAlgebra
    let := (integralScalarIntegerInclusion l E L ι).toAlgebra
    Nonempty (Module.Basis (Fin (Module.finrank E L))
      (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionIntegers l L)) := by
  classical
  let := ι.toAlgebra
  let := (integralScalarIntegerInclusion l E L ι).toAlgebra
  let A := Padic.coefficientExtensionIntegers l E
  let B := Padic.coefficientExtensionIntegers l L
  have : FiniteDimensional E L := Module.Finite.right ℚ_[l] E L
  obtain ⟨b, hb, hex⟩ := Padic.exists_integral_basis l E L
    (integralScalar_absoluteValue l E L ι)
  let v : Fin (Module.finrank E L) → B := fun j ↦ ⟨b j, hb j⟩
  let f : (Fin (Module.finrank E L) → A) →ₗ[A] B :=
    ∑ j, (LinearMap.proj j).smulRight (v j)
  have hf (c : Fin (Module.finrank E L) → A) :
      (f c : L) = ∑ j, ι (c j) * b j := by
    simp only [f, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
    change B.subtype (∑ j, c j • v j) = _
    rw [map_sum]
    rfl
  have hbije : Function.Bijective f := by
    constructor
    · intro c c' h
      obtain ⟨a, ha, huniq⟩ := hex (f c) (f c).property
      have hc : (fun j ↦ (c j : E)) = a := huniq _
        ⟨fun j ↦ (c j).property, hf c⟩
      have hc' : (fun j ↦ (c' j : E)) = a := huniq _
        ⟨fun j ↦ (c' j).property, (congrArg (fun z : B ↦ (z : L)) h).trans (hf c')⟩
      funext j
      apply Subtype.ext
      exact congrFun (hc.trans hc'.symm) j
    · intro x
      obtain ⟨a, ha, _⟩ := hex x x.property
      let c : Fin (Module.finrank E L) → A := fun j ↦ ⟨a j, ha.1 j⟩
      refine ⟨c, Subtype.ext ?_⟩
      exact (hf c).trans ha.2.symm
  exact ⟨Module.Basis.ofEquivFun (LinearEquiv.ofBijective f hbije).symm⟩
private theorem integral_ramification :
    ∃ (a : (Padic.coefficientExtensionIntegers l L)ˣ) (e : ℕ),
      1 ≤ e ∧ integralScalarIntegerInclusion l E L ι
        (Padic.coefficientExtensionUniformizer l E) =
          (a : Padic.coefficientExtensionIntegers l L) *
            Padic.coefficientExtensionUniformizer l L ^ e := by
  have hE := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hL := (Padic.coefficientExtensionIntegers_dvr l L).choose_spec
  let : IsLocalRing (Padic.coefficientExtensionIntegers l E) := hE.2.2.2.1
  let : IsLocalRing (Padic.coefficientExtensionIntegers l L) := hL.2.2.2.1
  let : IsDiscreteValuationRing (Padic.coefficientExtensionIntegers l E) :=
    hE.2.2.2.2.2.2.2.1
  let : IsDiscreteValuationRing (Padic.coefficientExtensionIntegers l L) :=
    hL.2.2.2.2.2.2.2.1
  have hgenE : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    hE.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hgenL : Ideal.span {Padic.coefficientExtensionUniformizer l L} =
      Padic.coefficientExtensionMaximalIdeal l L :=
    hL.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hiE : Irreducible (Padic.coefficientExtensionUniformizer l E) := by
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    exact (hE.2.2.2.2.2.1
      (IsLocalRing.maximalIdeal (Padic.coefficientExtensionIntegers l E))
      (IsLocalRing.maximalIdeal.isMaximal (Padic.coefficientExtensionIntegers l E))).trans
        hgenE.symm
  have hiL : Irreducible (Padic.coefficientExtensionUniformizer l L) := by
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    exact (hL.2.2.2.2.2.1
      (IsLocalRing.maximalIdeal (Padic.coefficientExtensionIntegers l L))
      (IsLocalRing.maximalIdeal.isMaximal (Padic.coefficientExtensionIntegers l L))).trans
        hgenL.symm
  have hx : integralScalarIntegerInclusion l E L ι
      (Padic.coefficientExtensionUniformizer l E) ≠ 0 := by
    intro h
    apply hiE.ne_zero
    apply Subtype.ext
    apply ι.injective
    change ι (Padic.coefficientExtensionUniformizer l E) = ι 0
    rw [map_zero]
    have hh := congrArg (fun x : Padic.coefficientExtensionIntegers l L ↦ (x : L)) h
    change ι (Padic.coefficientExtensionUniformizer l E) = 0 at hh
    exact hh
  obtain ⟨e, a, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hiL
  refine ⟨a, e, ?_, ha⟩
  by_contra he
  have he : e = 0 := by omega
  subst e
  have hmem : integralScalarIntegerInclusion l E L ι
      (Padic.coefficientExtensionUniformizer l E) ∈
      Padic.coefficientExtensionMaximalIdeal l L := by
    apply (hL.2.1 _).mpr
    change Padic.coefficientExtensionAbsoluteValue l L
      (ι (Padic.coefficientExtensionUniformizer l E)) < 1
    rw [integralScalar_absoluteValue l E L ι]
    apply (hE.2.1 _).mp
    change Padic.coefficientExtensionUniformizer l E ∈
      Padic.coefficientExtensionMaximalIdeal l E
    rw [← hgenE]
    exact Ideal.mem_span_singleton_self _
  have hunit : IsUnit (integralScalarIntegerInclusion l E L ι
      (Padic.coefficientExtensionUniformizer l E)) := by
    rw [ha, pow_zero, mul_one]
    exact a.isUnit
  exact hL.2.2.2.2.1.ne_top
    ((Padic.coefficientExtensionMaximalIdeal l L).eq_top_of_isUnit_mem hmem hunit)

end IntegralBasis

private noncomputable def liftedQuotient (A : Type u) [CommRing A] (a : A) (n : ℕ) :
    (ULift.{t + 1} A ⧸ (Ideal.span {ULift.up a}) ^ n) ≃+*
      ULift.{t + 1} (A ⧸ (Ideal.span {a}) ^ n) :=
  (Ideal.quotientEquiv _ _ ULift.ringEquiv (by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    rfl)).trans ULift.ringEquiv.symm

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})

private theorem scalarPreservesSheafification :
    (AlgebraicGeometry.Scheme.ProEt.topology Y).PreservesSheafification
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}) := by
  let : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf _
  let K := (equivSmallModel.{max u (t + 1)} Y.ProEt).inverse.inducedTopology
    (AlgebraicGeometry.Scheme.ProEt.topology Y)
  let : K.PreservesSheafification
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}) :=
    GrothendieckTopology.instPreservesSheafification K _
      (FD := fun A B : CommRingCat.{max u (t + 1)} ↦ A →+* B)
      (CD := fun A : CommRingCat.{max u (t + 1)} ↦ A)
      (FE := fun A B : RingCat.{max u (t + 1)} ↦ A →+* B)
      (CE := fun A : RingCat.{max u (t + 1)} ↦ A)
  exact GrothendieckTopology.PreservesSheafification.transport
    (AlgebraicGeometry.Scheme.ProEt.topology Y) K
    (equivSmallModel.{max u (t + 1)} Y.ProEt).inverse _ _
attribute [local instance] scalarPreservesSheafification

private theorem mapped_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (G : C ⥤ D) (H : D ⥤ B) (V : C ⥤ A)
    (c : G ⋙ H ≅ V ⋙ F) {X Y : C} {X' Y' : A}
    (eX : X' ≅ V.obj X) (eY : Y' ≅ V.obj Y) (f : X' ⟶ Y') (g : X ⟶ Y)
    (h : f ≫ eY.hom = eX.hom ≫ V.map g) :
    F.map f ≫ (F.map eY.hom ≫ c.inv.app Y) =
      (F.map eX.hom ≫ c.inv.app X) ≫ H.map (G.map g) := by
  have hc := c.inv.naturality g
  change F.map (V.map g) ≫ c.inv.app Y = c.inv.app X ≫ H.map (G.map g) at hc
  rw [← Category.assoc, ← F.map_comp, h, F.map_comp, Category.assoc, hc,
    ← Category.assoc]

private noncomputable def finitePresentation (n : ℕ) :
    adicBasisResidue.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
        (ULift.up (Padic.coefficientExtensionUniformizer l E)) n ≅
      integralCoefficientSheaf l E Y n :=
  (constantSheaf (AlgebraicGeometry.Scheme.ProEt.topology Y)
    RingCat.{max u (t + 1)}).mapIso
      (RingEquiv.toRingCatIso (liftedQuotient
        (Padic.coefficientExtensionIntegers l E)
        (Padic.coefficientExtensionUniformizer l E) (n + 1))) ≪≫
    ((constantCommuteCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).app
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).symm

private theorem finitePresentation_naturality (n : ℕ) :
    (adicBasisTower.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
      (ULift.up (Padic.coefficientExtensionUniformizer l E))).map
        (homOfLE (Nat.le_succ n)).op ≫ (finitePresentation l E Y n).hom =
    (finitePresentation l E Y (n + 1)).hom ≫ integralCoefficientSheafTransition l E Y n := by
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let CR := constantSheaf J RingCat.{max u (t + 1)}
  let CC := constantSheaf J CommRingCat.{max u (t + 1)}
  let FC := sheafCompose J (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let c := constantCommuteCompose J
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let q : CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 2))) ⟶
      CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))) :=
    CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((Padic.coefficientExtensionTransition l E (n + 1)).comp ULift.ringEquiv.toRingHom))
  apply mapped_square CR CC FC (forget₂ CommRingCat RingCat) c
    (RingEquiv.toRingCatIso (liftedQuotient
      (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionUniformizer l E) (n + 2)))
    (RingEquiv.toRingCatIso (liftedQuotient
      (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionUniformizer l E) (n + 1))) _ q
  ext x
  rfl

private noncomputable def towerPresentation :
    adicBasisTower.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
      (ULift.up (Padic.coefficientExtensionUniformizer l E)) ≅
        integralCoefficientSheafSystem l E Y := by
  let f : adicBasisTower.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
      (ULift.up (Padic.coefficientExtensionUniformizer l E)) ⟶
        integralCoefficientSheafSystem l E Y :=
    NatTrans.ofOpSequence (fun n ↦ (finitePresentation l E Y n).hom)
    (fun n ↦ by
      simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ]
        using finitePresentation_naturality l E Y n)
  have : ∀ X, IsIso (f.app X) := fun X ↦ by
    change IsIso (finitePresentation l E Y X.unop).hom
    infer_instance
  have : IsIso f := NatIso.isIso_of_isIso_app f
  exact asIso f

private noncomputable def completionPresentation :
    adicBasisCompletion.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
      (ULift.up (Padic.coefficientExtensionUniformizer l E)) ≅
        completedIntegralCoefficientSheafUnrestricted l E Y :=
  lim.mapIso (towerPresentation l E Y)

private theorem completionPresentation_projection (n : ℕ) :
    (completionPresentation l E Y).hom ≫
      limit.π (integralCoefficientSheafSystem l E Y) (op n) =
    adicBasisProjection.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
        (ULift.up (Padic.coefficientExtensionUniformizer l E)) n ≫
      (finitePresentation l E Y n).hom := by
  simpa only [completionPresentation, Functor.mapIso_hom, adicBasisProjection, limMap_eq,
    towerPresentation, asIso_hom, NatTrans.ofOpSequence_app] using
      limMap_π (towerPresentation l E Y).hom (op n)

variable (L : Type u) [Field L] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)

private theorem finitePresentation_scalar (n : ℕ)
    (a : (ULift.{t + 1} (Padic.coefficientExtensionIntegers l L))ˣ)
    (e : ℕ) (he : 1 ≤ e)
    (ht : let := (integralScalarIntegerInclusion l E L ι).toAlgebra
      let : Algebra (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
        (Padic.coefficientExtensionIntegers l L) :=
      ULift.algebra' (Padic.coefficientExtensionIntegers l E)
        (Padic.coefficientExtensionIntegers l L)
      algebraMap (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
          (ULift.{t + 1} (Padic.coefficientExtensionIntegers l L))
          (ULift.up (Padic.coefficientExtensionUniformizer l E)) =
        (a : ULift.{t + 1} (Padic.coefficientExtensionIntegers l L)) *
          (ULift.up (Padic.coefficientExtensionUniformizer l L)) ^ e) :
    let := (integralScalarIntegerInclusion l E L ι).toAlgebra
    let : Algebra (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
        (Padic.coefficientExtensionIntegers l L) :=
      ULift.algebra' (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l L)
    adicBasisScalar.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (ULift.up (Padic.coefficientExtensionUniformizer l E))
        (ULift.up (Padic.coefficientExtensionUniformizer l L)) a e he ht n ≫
          (finitePresentation l L Y n).hom =
      (finitePresentation l E Y n).hom ≫
        (sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (forget₂ CommRingCat RingCat)).map (integralScalarQuotientSheafMap l E L ι Y n) := by
  let := (integralScalarIntegerInclusion l E L ι).toAlgebra
  let : Algebra (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
        (Padic.coefficientExtensionIntegers l L) :=
      ULift.algebra' (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionIntegers l L)
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let CR := constantSheaf J RingCat.{max u (t + 1)}
  let CC := constantSheaf J CommRingCat.{max u (t + 1)}
  let FC := sheafCompose J (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let c := constantCommuteCompose J
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let q := CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((integralScalarQuotientMap l E L ι n).comp ULift.ringEquiv.toRingHom))
  apply mapped_square CR CC FC (forget₂ CommRingCat RingCat) c
    (RingEquiv.toRingCatIso (liftedQuotient
      (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionUniformizer l E) (n + 1)))
    (RingEquiv.toRingCatIso (liftedQuotient
      (Padic.coefficientExtensionIntegers l L)
      (Padic.coefficientExtensionUniformizer l L) (n + 1))) _ q
  ext x
  rfl

/-- The completed target coefficient sheaf is free of the relative field degree, with
its action given by the unique map having the prescribed finite reductions.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-weil-completed-integral-finite-free).
Proof: an integral basis gives a basis over the integer DVR. Its uniformizer maps to a
unit times a positive power of the target uniformizer. Lift the basis to the coefficient
universe and apply the adic basis limit theorem. The quotient equivalences commute with
all transitions and the finite scalar maps. Their limit isomorphisms therefore identify
the adic scalar map with the specified completed map, by joint monicity of the limit
projections. Restricting along the ring isomorphisms transports the basis and its action.
-/
theorem completedIntegralFiniteFree
    (φ : completedIntegralCommRingSheafUnrestricted l E Y ⟶
      completedIntegralCommRingSheafUnrestricted l L Y)
    (hφ : ∀ n : ℕ, φ ≫ completedIntegralCommRingProjectionUnrestricted l L Y n =
      completedIntegralCommRingProjectionUnrestricted l E Y n ≫
        integralScalarQuotientSheafMap l E L ι Y n) :
    let := ι.toAlgebra
    Nonempty
      ((SheafOfModules.restrictScalars
        ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map φ)).obj
            (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l L Y)) ≅
        ∏ᶜ fun _ : Fin (Module.finrank E L) ↦
          SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y)) := by
  classical
  let := ι.toAlgebra
  let := (integralScalarIntegerInclusion l E L ι).toAlgebra
  let : Algebra (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
        (Padic.coefficientExtensionIntegers l L) :=
      ULift.algebra' (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionIntegers l L)
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let FC := sheafCompose J
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  obtain ⟨b⟩ := integral_basis l E L ι
  obtain ⟨a, e, he, ht⟩ := integral_ramification l E L ι
  let a' : (ULift.{t + 1} (Padic.coefficientExtensionIntegers l L))ˣ :=
    Units.map ULift.ringEquiv.symm.toMonoidHom a
  have ht' : algebraMap (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
      (ULift.{t + 1} (Padic.coefficientExtensionIntegers l L))
        (ULift.up (Padic.coefficientExtensionUniformizer l E)) =
      (a' : ULift.{t + 1} (Padic.coefficientExtensionIntegers l L)) *
        (ULift.up (Padic.coefficientExtensionUniformizer l L)) ^ e := by
    apply ULift.ext
    exact ht
  obtain ⟨f, hf, _, Φ, _⟩ := adic_basis_limit.{t + 1, t, u} J _ (liftedBasis b)
    (ULift.up (Padic.coefficientExtensionUniformizer l E))
    (ULift.up (Padic.coefficientExtensionUniformizer l L)) a' e he ht'
  have hproj (F : Type u) [Field F] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F] (n : ℕ) :
      FC.map (completedIntegralCommRingProjectionUnrestricted l F Y n) =
        limit.π (integralCoefficientSheafSystem l F Y) (op n) := by
    ext U x
    rfl
  have h : f ≫ (completionPresentation l L Y).hom =
      (completionPresentation l E Y).hom ≫ FC.map φ := by
    apply limit.hom_ext
    intro n
    have hφr := congrArg FC.map (hφ n.unop)
    simp only [Functor.map_comp, hproj] at hφr
    rw [Category.assoc, completionPresentation_projection, ← Category.assoc, hf n.unop,
      Category.assoc, finitePresentation_scalar l E Y L ι n.unop a' e he ht',
      ← Category.assoc, ← completionPresentation_projection, Category.assoc, ← hφr,
      ← Category.assoc]
  exact freeTransport (completionPresentation l E Y) (completionPresentation l L Y)
    f (FC.map φ) h _ Φ.symm

end WeilConjectures
