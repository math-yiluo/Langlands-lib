/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Injective.ExtHomology
public import WeilConjectures.CategoryTheory.Preadditive.Injective.ResolutionMap
public import WeilConjectures.SixFunctors.ProEtale.Adic.GlobalSectionsExt
public import WeilConjectures.WeilSheaf.CohomologyResolution
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.CategoryTheory.Sites.SheafSmul
public import WeilConjectures.SixFunctors.ProEtale.Adic.ExtFrobenius

/-!
# Weil cohomology of the constant sheaf as pro-étale `Ext`

The cohomology `Hʳ(Y ⊗ k̄, ℚ̄_ℓ)` of the constant Weil sheaf is the pro-étale cohomology
`Hʳ(Ȳ_proét, ℚ̄_ℓ) = Ext^r(ℤ, ℚ̄_ℓ,Ȳ)` of the underlying abelian sheaf, computed through an
injective resolution `I` of `ℚ̄_ℓ` by pro-étale Weil sheaves, whose underlying abelian sheaves
form an injective resolution of `ℚ̄_ℓ,Ȳ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor Opposite Abelian

namespace CategoryTheory.InjectiveResolution

/-- A map of resolutions acting by a scalar on sections acts by that scalar on homology. -/
private lemma extAddEquivHomology_comp_mk₀
    {C : Type*} [Category* C] [Abelian C] [HasExt C] {X Y : C}
    (R : InjectiveResolution Y) {A : Type*} [Ring A] {n : ℕ}
    (S : ShortComplex (ModuleCat A))
    (e₂ : (X ⟶ R.cocomplex.X n) ≃+ S.X₂)
    (e₃ : (X ⟶ R.cocomplex.X (n + 1)) ≃+ S.X₃)
    (hg : ∀ f, S.g (e₂ f) = e₃ (f ≫ R.cocomplex.d n (n + 1)))
    (hbd : ∀ f (hf : f ≫ R.cocomplex.d n (n + 1) = 0),
      R.extMk f (n + 1) rfl hf = 0 ↔ ∃ x : S.X₁, S.f x = e₂ f)
    {g : Y ⟶ Y} (φ : Hom R R g) (a : A)
    (ha : ∀ f, e₂ (f ≫ φ.hom.f n) = a • e₂ f) (x : Ext X Y n) :
    extAddEquivHomology R S e₂ e₃ hg hbd (x.comp (Ext.mk₀ g) (add_zero n)) =
      a • extAddEquivHomology R S e₂ e₃ hg hbd x := by
  obtain ⟨f, hf, rfl⟩ := R.extMk_surjective x (n + 1) rfl
  obtain ⟨z, hz⟩ := S.moduleCat_exists_iCycles (e₂ f)
    (g_eq_zero_of_cocycle R S e₂ e₃ hg f hf)
  rw [extMk_comp_mk₀ f (n + 1) rfl hf φ,
    extAddEquivHomology_extMk R S e₂ e₃ hg hbd f hf z hz,
    extAddEquivHomology_extMk R S e₂ e₃ hg hbd _ _ (a • z)
      (by rw [map_smul, hz, ha]), map_smul]

end CategoryTheory.InjectiveResolution

private lemma equiv_trans_symm_intertwines {A B C : Type*} (e : A ≃ B) (f : C ≃ B)
    (a : A → A) (b : B → B) (c : C → C)
    (he : ∀ x, e (a x) = b (e x)) (hf : ∀ x, f (c x) = b (f x)) (x : A) :
    e.trans f.symm (a x) = c (e.trans f.symm x) := by
  apply f.injective
  exact (f.apply_symm_apply _).trans ((he x).trans
    ((congrArg b (f.apply_symm_apply _).symm).trans (hf _).symm))

namespace AlgebraicGeometry

attribute [local instance 2000] CategoryWithHomology.hasHomology
  ShortComplex.hasLeftHomology_of_hasHomology

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

namespace ProEtaleWeilSheaf

variable (k₀ l) (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k₀))]

/-- The underlying abelian sheaf of a pro-étale Weil sheaf. -/
noncomputable abbrev forgetAb :
    ProEtaleWeilSheaf k₀ l Y ⥤
      Sheaf (Scheme.ProEt.topology (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        AddCommGrpCat.{u + 1} :=
  IsoAlgebra.forget _ ⋙ AdicSheaf.forget _ ⋙ sheafForget₂ (ULift.{u + 1} (PadicAlgCl l)) _


instance preservesInjectiveObjects_adicSheafForget (X : Scheme.{u}) :
    (AdicSheaf.forget (l := l) X).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Mod.freeForgetAdjunction (adicConstantSheaf l X))

instance preservesInjectiveObjects_forgetAb : (forgetAb k₀ l Y).PreservesInjectiveObjects := by
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsoAlgebra.preservesInjectiveObjects_forget (F := WeilSheaf.frobeniusPullback k₀ l Y)
  infer_instance

end ProEtaleWeilSheaf

namespace ProEtaleWeilSheaf

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]

/-- Morphisms `ℤ ⟶ M` out of the constant abelian sheaf, for a pro-étale Weil sheaf `M`, are the
global sections `Γ(Ȳ, M)`. -/
noncomputable def sectionsAddEquiv (M : ProEtaleWeilSheaf k₀ l Y) :
    (constantIntSheaf _ ⟶ (forgetAb k₀ l Y).obj M) ≃+ (globalSectionsWeilFunctor k₀ l Y).obj M :=
  constantIntHomAddEquivΓ _ M.carrier.X

lemma sectionsAddEquiv_comp {M M' : ProEtaleWeilSheaf k₀ l Y}
    (f : constantIntSheaf _ ⟶ (forgetAb k₀ l Y).obj M) (φ : M ⟶ M') :
    sectionsAddEquiv M' (f ≫ (forgetAb k₀ l Y).map φ) =
      (globalSectionsWeilFunctor k₀ l Y).map φ (sectionsAddEquiv M f) :=
  constantIntHomAddEquivΓ_comp f _

/-- `sectionsAddEquiv` after an isomorphism of the target. -/
noncomputable def sectionsAddEquivOfIso {M M' : ProEtaleWeilSheaf k₀ l Y} (e : M ≅ M') :
    (constantIntSheaf _ ⟶ (forgetAb k₀ l Y).obj M) ≃+ (globalSectionsWeilFunctor k₀ l Y).obj M' :=
  (AddEquiv.mk' ((Iso.refl _).homCongr ((forgetAb k₀ l Y).mapIso e)) fun f g ↦ by simp).trans
    (sectionsAddEquiv M')

lemma sectionsAddEquivOfIso_apply {M M' : ProEtaleWeilSheaf k₀ l Y} (e : M ≅ M')
    (f : constantIntSheaf _ ⟶ (forgetAb k₀ l Y).obj M) :
    sectionsAddEquivOfIso e f = sectionsAddEquiv M' (f ≫ (forgetAb k₀ l Y).map e.hom) := by
  rw [sectionsAddEquivOfIso, AddEquiv.trans_apply]
  congr 1

variable {K : ProEtaleWeilSheaf k₀ l Y} (I : InjectiveResolution K) (r : ℕ)

lemma sc_g_sectionsAddEquiv (f : constantIntSheaf _ ⟶ (forgetAb k₀ l Y).obj (I.cocomplex.X r)) :
    ((I.cocomplex.sc r).map (globalSectionsWeilFunctor k₀ l Y)).g (sectionsAddEquiv _ f) =
      sectionsAddEquivOfIso (I.cocomplex.XIsoOfEq (CochainComplex.next ℕ r).symm)
        (f ≫ ((I.map (forgetAb k₀ l Y)).cocomplex.d r (r + 1))) := by
  rw [sectionsAddEquivOfIso_apply, Category.assoc]
  rw [InjectiveResolution.map_cocomplex_d,
    ← (forgetAb k₀ l Y).map_comp, HomologicalComplex.d_comp_XIsoOfEq_hom,
    sectionsAddEquiv_comp]
  rfl

private lemma sc_f_sectionsAddEquiv (p : ℕ)
    (g : constantIntSheaf _ ⟶ (forgetAb k₀ l Y).obj (I.cocomplex.X p)) :
    ((I.cocomplex.sc (p + 1)).map (globalSectionsWeilFunctor k₀ l Y)).f
      (sectionsAddEquivOfIso (I.cocomplex.XIsoOfEq (CochainComplex.prev_nat_succ p).symm) g) =
      sectionsAddEquiv _ (g ≫ (forgetAb k₀ l Y).map (I.cocomplex.d p (p + 1))) := by
  rw [sectionsAddEquivOfIso_apply]
  refine (sectionsAddEquiv_comp _ (I.cocomplex.d _ (p + 1))).symm.trans ?_
  have hd := congrArg (forgetAb k₀ l Y).map
    (I.cocomplex.XIsoOfEq_hom_comp_d (CochainComplex.prev_nat_succ p).symm (p + 1))
  rw [Functor.map_comp] at hd
  rw [Category.assoc, hd]

lemma extMk_eq_zero_iff_sectionsAddEquiv
    (f : constantIntSheaf _ ⟶ (I.map (forgetAb k₀ l Y)).cocomplex.X r)
    (hf : f ≫ (I.map (forgetAb k₀ l Y)).cocomplex.d r (r + 1) = 0) :
    (I.map (forgetAb k₀ l Y)).extMk f (r + 1) rfl hf = 0 ↔
      ∃ x : ((I.cocomplex.sc r).map (globalSectionsWeilFunctor k₀ l Y)).X₁,
        ((I.cocomplex.sc r).map (globalSectionsWeilFunctor k₀ l Y)).f x = sectionsAddEquiv _ f := by
  cases r with
  | zero =>
    refine (InjectiveResolution.extMk_eq_zero_iff_of_zero _ f hf).trans ?_
    have h0 : I.cocomplex.d ((ComplexShape.up ℕ).prev 0) 0 = 0 :=
      I.cocomplex.shape _ _ (by simp)
    have hz (x) : ((I.cocomplex.sc 0).map (globalSectionsWeilFunctor k₀ l Y)).f x = 0 :=
      ConcreteCategory.congr_hom ((ShortComplex.map_f _ _).trans
        ((congrArg (globalSectionsWeilFunctor k₀ l Y).map h0).trans
          ((globalSectionsWeilFunctor k₀ l Y).map_zero _ _))) x
    exact ⟨fun h ↦ ⟨0, (hz 0).trans
      (((sectionsAddEquiv (I.cocomplex.X 0)).map_zero).symm.trans
        (congrArg (sectionsAddEquiv (I.cocomplex.X 0)) h.symm))⟩,
      fun ⟨x, hx⟩ ↦ (sectionsAddEquiv (I.cocomplex.X 0)).injective
        (hx.symm.trans ((hz x).trans ((sectionsAddEquiv (I.cocomplex.X 0)).map_zero).symm))⟩
  | succ p =>
    refine (InjectiveResolution.extMk_eq_zero_iff _ f _ rfl hf p rfl).trans ?_
    rw [InjectiveResolution.map_cocomplex_d]
    refine (sectionsAddEquivOfIso
      (I.cocomplex.XIsoOfEq (CochainComplex.prev_nat_succ p).symm)).toEquiv.exists_congr
        (fun g ↦ ?_)
    exact (sectionsAddEquiv (I.cocomplex.X (p + 1))).injective.eq_iff.symm.trans
      (congrArg (fun z ↦ z = sectionsAddEquiv (I.cocomplex.X (p + 1)) f)
        (sc_f_sectionsAddEquiv I p g)).to_iff.symm

/-- The `r`-th pro-étale `Ext` of `ℤ` into the underlying abelian sheaf of a pro-étale Weil sheaf
`K` is the `r`-th homology of the complex of global sections of an injective resolution of `K`. -/
noncomputable def extAddEquivHomology :
    Ext (constantIntSheaf _) ((forgetAb k₀ l Y).obj K) r ≃+
      ((I.cocomplex.sc r).map (globalSectionsWeilFunctor k₀ l Y)).homology :=
  InjectiveResolution.extAddEquivHomology (I.map (forgetAb k₀ l Y)) _ (sectionsAddEquiv _)
    (sectionsAddEquivOfIso (I.cocomplex.XIsoOfEq (CochainComplex.next ℕ r).symm))
    (sc_g_sectionsAddEquiv I r) (extMk_eq_zero_iff_sectionsAddEquiv I r)

variable (k₀ l Y) in
/-- Multiplication by a scalar `c ∈ ℚ̄_ℓ` on the underlying abelian sheaves of pro-étale Weil
sheaves. -/
@[simps]
noncomputable def smulNatTrans (c : PadicAlgCl l) : forgetAb k₀ l Y ⟶ forgetAb k₀ l Y where
  app M := (sheafForget₂ _ _).map (Sheaf.smulEnd M.carrier.X (ULift.up c))
  naturality M M' φ := by
    simp only [Functor.comp_map]
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (Sheaf.smulEnd_comp _ _).symm

lemma sectionsAddEquiv_comp_smulNatTrans (c : PadicAlgCl l) {M : ProEtaleWeilSheaf k₀ l Y}
    (f : constantIntSheaf _ ⟶ (forgetAb k₀ l Y).obj M) :
    sectionsAddEquiv M (f ≫ (smulNatTrans k₀ l Y c).app M) =
      (ULift.up c : ULift.{u + 1} (PadicAlgCl l)) • sectionsAddEquiv M f := by
  refine (constantIntHomAddEquivΓ_comp f _).trans ?_
  exact Sheaf.Γ_map_smulEnd.{u + 1} (J := Scheme.ProEt.topology _)
    (Scheme.ProEt.isTerminalMkId _) _ _ _

lemma extAddEquivHomology_extMk
    (f : constantIntSheaf _ ⟶ (I.map (forgetAb k₀ l Y)).cocomplex.X r)
    (hf : f ≫ (I.map (forgetAb k₀ l Y)).cocomplex.d r (r + 1) = 0)
    (c : ((I.cocomplex.sc r).map (globalSectionsWeilFunctor k₀ l Y)).cycles)
    (hc : ((I.cocomplex.sc r).map (globalSectionsWeilFunctor k₀ l Y)).iCycles c =
      sectionsAddEquiv _ f) :
    extAddEquivHomology I r ((I.map (forgetAb k₀ l Y)).extMk f (r + 1) rfl hf) =
      ((I.cocomplex.sc r).map (globalSectionsWeilFunctor k₀ l Y)).homologyπ c :=
  InjectiveResolution.extAddEquivHomology_extMk _ _ _ _ _ _ f hf c hc

set_option maxRecDepth 4000 in
/-- `extAddEquivHomology` is `ℚ̄_ℓ`-linear: multiplication by `c` on the coefficients corresponds
to multiplication by `c` on the homology of the global sections. -/
lemma extAddEquivHomology_comp_smul (c : PadicAlgCl l)
    (x : Ext (constantIntSheaf _) ((forgetAb k₀ l Y).obj K) r) :
    extAddEquivHomology I r (x.comp (Ext.mk₀ ((smulNatTrans k₀ l Y c).app K)) (add_zero r)) =
      (ULift.up c : ULift.{u + 1} (PadicAlgCl l)) • extAddEquivHomology I r x := by
  exact InjectiveResolution.extAddEquivHomology_comp_mk₀
    (I.map (forgetAb k₀ l Y)) (n := r)
    ((I.cocomplex.sc r).map (globalSectionsWeilFunctor k₀ l Y))
    (sectionsAddEquiv (I.cocomplex.X r))
    (sectionsAddEquivOfIso (I.cocomplex.XIsoOfEq (CochainComplex.next ℕ r).symm))
    (sc_g_sectionsAddEquiv I r) (extMk_eq_zero_iff_sectionsAddEquiv I r)
    (InjectiveResolution.mapHomOfNatTrans (smulNatTrans k₀ l Y c) I) (ULift.up c)
    (sectionsAddEquiv_comp_smulNatTrans c (M := I.cocomplex.X r)) x

lemma smulNatTrans_app_adicConstant (c : PadicAlgCl l) :
    (smulNatTrans k₀ l Y c).app (ProEtaleWeilSheaf.adicConstant k₀ l Y) =
      adicScalar l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber c :=
  rfl

variable (k₀ l Y) in
/-- The structure isomorphisms `Fr^* M ≅ M` of pro-étale Weil sheaves, on the underlying abelian
sheaves: `(Fr⁻¹)_* M ⟶ M`. -/
noncomputable def strForgetAb :
    forgetAb k₀ l Y ⋙
        ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[AddCommGrpCat.{u + 1}]
      ⟶ forgetAb k₀ l Y :=
  Functor.whiskerRight (IsoAlgebra.strNatIso (WeilSheaf.frobeniusPullback k₀ l Y)).hom
    (AdicSheaf.forget _ ⋙ sheafForget₂ (ULift.{u + 1} (PadicAlgCl l)) _)

/-- The Frobenius on the cocycles `ℤ ⟶ Iⁿ` of the complex computing `Ext(ℤ, K)`: the Frobenius of
the global sections `Γ(Ȳ, Iⁿ)`. -/
noncomputable def cocycleFrobenius (n : ℕ) :
    (constantIntSheaf _ ⟶ (I.map (forgetAb k₀ l Y)).cocomplex.X n) →+
      (constantIntSheaf _ ⟶ (I.map (forgetAb k₀ l Y)).cocomplex.X n) :=
  ((sectionsAddEquiv (I.cocomplex.X n)).symm.toAddMonoidHom.comp
    ((globalSectionsFrobeniusNatTrans k₀ l Y).app (I.cocomplex.X n)).hom.toAddMonoidHom).comp
      (sectionsAddEquiv (I.cocomplex.X n)).toAddMonoidHom

lemma sectionsAddEquiv_cocycleFrobenius (n : ℕ)
    (f : constantIntSheaf _ ⟶ (I.map (forgetAb k₀ l Y)).cocomplex.X n) :
    sectionsAddEquiv _ (cocycleFrobenius I n f) =
      (globalSectionsFrobeniusNatTrans k₀ l Y).app (I.cocomplex.X n) (sectionsAddEquiv _ f) :=
  AddEquiv.apply_symm_apply _ _

lemma cocycleFrobenius_comp_d (n m : ℕ)
    (f : constantIntSheaf _ ⟶ (I.map (forgetAb k₀ l Y)).cocomplex.X n) :
    cocycleFrobenius I m (f ≫ (I.map (forgetAb k₀ l Y)).cocomplex.d n m) =
      cocycleFrobenius I n f ≫ (I.map (forgetAb k₀ l Y)).cocomplex.d n m := by
  refine (sectionsAddEquiv _).injective ?_
  rw [sectionsAddEquiv_cocycleFrobenius, InjectiveResolution.map_cocomplex_d,
    sectionsAddEquiv_comp, sectionsAddEquiv_comp, sectionsAddEquiv_cocycleFrobenius]
  have h := ConcreteCategory.congr_hom
    ((globalSectionsFrobeniusNatTrans k₀ l Y).naturality (I.cocomplex.d n m)) (sectionsAddEquiv _ f)
  simp only [ConcreteCategory.comp_apply] at h
  exact h

-- the pushforward of the underlying abelian sheaf is only definitionally that of the sheaf
/-- The Frobenius of the global sections of the terms of `I` on the cocycles `ℤ ⟶ Iⁿ` is
`f ↦ (ℤ ⟶ Fr⁻¹_* ℤ) ≫ Fr⁻¹_* f ≫ φ`, `φ` the structure isomorphism of `Iⁿ`. -/
lemma cocycleFrobenius_eq_resolutionFrobeniusCocycle (n : ℕ)
    (f : constantIntSheaf _ ⟶ (I.map (forgetAb k₀ l Y)).cocomplex.X n) :
    cocycleFrobenius I n f = resolutionFrobeniusCocycle
      (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
      (InjectiveResolution.mapMapHomOfNatTrans (strForgetAb k₀ l Y) I) n f := by
  apply (sectionsAddEquiv _).injective
  have h₂ := constantIntHomAddEquivΓ_constantIntSheafToLowerStar_comp
    (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv (I.cocomplex.X n).carrier.X f
  have h₃ := constantIntHomAddEquivΓ_comp
    (M :=
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u}
        l].obj
      (I.cocomplex.X n).carrier.X) (N := (I.cocomplex.X n).carrier.X) (constantIntSheafToLowerStar
    (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv ≫
      ((Y ↘ Spec
        (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[AddCommGrpCat.{u + 1}].map f)
    ((AdicSheaf.forget _).map (I.cocomplex.X n).str.hom)
  rw [h₂, Category.assoc] at h₃
  rw [sectionsAddEquiv_cocycleFrobenius]
  exact h₃.symm

/-- The Frobenius on `Ext(ℤ, K)` induced by the Frobenius of the global sections of the terms of
an injective resolution of `K`. -/
noncomputable def extFrobenius :
    Ext (constantIntSheaf _) ((forgetAb k₀ l Y).obj K) r →+
      Ext (constantIntSheaf _) ((forgetAb k₀ l Y).obj K) r :=
  InjectiveResolution.extMap (I.map (forgetAb k₀ l Y)) (cocycleFrobenius I)
    (cocycleFrobenius_comp_d I) r

/-- `extFrobenius` is the Frobenius on `Ext` induced by the structure isomorphisms of the terms of
the resolution, in the form of `AlgebraicGeometry.ProEtale.extFrobeniusOfResolution`. -/
lemma extFrobenius_eq_extFrobeniusOfResolution :
    extFrobenius I r = extFrobeniusOfResolution
      (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
      (InjectiveResolution.mapMapHomOfNatTrans (strForgetAb k₀ l Y) I) r := by
  have h : cocycleFrobenius I = resolutionFrobeniusCocycle
      (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
      (InjectiveResolution.mapMapHomOfNatTrans (strForgetAb k₀ l Y) I) :=
    funext fun n ↦ AddMonoidHom.ext (cocycleFrobenius_eq_resolutionFrobeniusCocycle I n)
  exact InjectiveResolution.extMap_congr _ _ _ _ h r

set_option maxRecDepth 4000 in
/-- Through `extAddEquivHomology`, the Frobenius `extFrobenius` is the map induced on homology by
the Frobenius of the global sections. -/
lemma extAddEquivHomology_extFrobenius (x : Ext (constantIntSheaf _) ((forgetAb k₀ l Y).obj K) r) :
    extAddEquivHomology I r (extFrobenius I r x) =
      ShortComplex.homologyMap ((I.cocomplex.sc r).mapNatTrans
        (globalSectionsFrobeniusNatTrans k₀ l Y)) (extAddEquivHomology I r x) :=
  InjectiveResolution.extAddEquivHomology_extMap (sc_g_sectionsAddEquiv I r)
    (extMk_eq_zero_iff_sectionsAddEquiv I r) (sc_g_sectionsAddEquiv I r)
    (extMk_eq_zero_iff_sectionsAddEquiv I r) (cocycleFrobenius I) (cocycleFrobenius_comp_d I)
    ((I.cocomplex.sc r).mapNatTrans (globalSectionsFrobeniusNatTrans k₀ l Y))
    (fun f ↦ (sectionsAddEquiv_cocycleFrobenius I r f).symm) x

end ProEtaleWeilSheaf

namespace WeilSheaf

variable [Fact (ringChar k₀ ≠ l)] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- **Weil cohomology of `ℚ̄_ℓ` is pro-étale cohomology, with its Frobenius.** For an injective
resolution `I` of the constant Weil sheaf, `Hʳ(Ȳ_proét, ℚ̄_ℓ) ≅ Hʳ(Y ⊗ k̄, ℚ̄_ℓ)`, the geometric
Frobenius corresponding to the Frobenius `ProEtaleWeilSheaf.extFrobenius I r` induced by the
Frobenius of the global sections of the terms of `I`. -/
theorem exists_addEquiv_adicConstantH_cohomology
    (I : InjectiveResolution (WeilSheaf.adicConstant k₀ l Y).obj) (r : ℕ) :
    ∃ Θ : Abelian.Ext (ProEtale.constantIntSheaf _)
        ((ProEtaleWeilSheaf.forgetAb k₀ l Y).obj (WeilSheaf.adicConstant k₀ l Y).obj) r ≃+
        ((WeilSheaf.adicConstant k₀ l Y).cohomology r).carrier,
      ∀ x, Θ (ProEtaleWeilSheaf.extFrobenius I r x) =
        ((WeilSheaf.adicConstant k₀ l Y).cohomology r).frobenius (Θ x) := by
  obtain ⟨Θ, hΘ⟩ := exists_linearEquiv_cohomology_resolution (WeilSheaf.adicConstant k₀ l Y) I r
  refine ⟨(ProEtaleWeilSheaf.extAddEquivHomology I r).trans Θ.toAddEquiv.symm, fun x ↦ ?_⟩
  exact equiv_trans_symm_intertwines
    (ProEtaleWeilSheaf.extAddEquivHomology I r).toEquiv Θ.toEquiv _ _ _
    (ProEtaleWeilSheaf.extAddEquivHomology_extFrobenius I r) hΘ x

/-- **Weil cohomology of `ℚ̄_ℓ` is pro-étale cohomology, `ℚ̄_ℓ`-linearly, with its Frobenius.**
For an injective resolution `I` of the constant Weil sheaf,
`Hʳ(Ȳ_proét, ℚ̄_ℓ) ≅ Hʳ(Y ⊗ k̄, ℚ̄_ℓ)` as `ℚ̄_ℓ`-vector spaces, the geometric Frobenius
corresponding to the Frobenius `ProEtaleWeilSheaf.extFrobenius I r` induced by the Frobenius of
the global sections of the terms of `I`. -/
theorem exists_linearEquiv_adicConstantH_cohomology
    (I : InjectiveResolution (WeilSheaf.adicConstant k₀ l Y).obj) (r : ℕ) :
    ∃ Θ : AdicConstantH l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber r ≃ₗ[PadicAlgCl l]
        ((WeilSheaf.adicConstant k₀ l Y).cohomology r).carrier,
      ∀ x, Θ (ProEtaleWeilSheaf.extFrobenius I r x) =
        ((WeilSheaf.adicConstant k₀ l Y).cohomology r).frobenius (Θ x) := by
  obtain ⟨Θ, hΘ⟩ := exists_linearEquiv_cohomology_resolution (WeilSheaf.adicConstant k₀ l Y) I r
  let Θa := (ProEtaleWeilSheaf.extAddEquivHomology I r).trans Θ.toAddEquiv.symm
  have key (x : Abelian.Ext (ProEtale.constantIntSheaf _)
      ((ProEtaleWeilSheaf.forgetAb k₀ l Y).obj (WeilSheaf.adicConstant k₀ l Y).obj) r) :
      Θa (ProEtaleWeilSheaf.extFrobenius I r x) =
        ((WeilSheaf.adicConstant k₀ l Y).cohomology r).frobenius (Θa x) := by
    exact equiv_trans_symm_intertwines
      (ProEtaleWeilSheaf.extAddEquivHomology I r).toEquiv Θ.toEquiv _ _ _
      (ProEtaleWeilSheaf.extAddEquivHomology_extFrobenius I r) hΘ x
  refine ⟨{ Θa with
    map_smul' := fun c x ↦ ?_ }, fun x ↦ ?_⟩
  · exact (congrArg Θ.symm (ProEtaleWeilSheaf.extAddEquivHomology_comp_smul I r c x)).trans
      (Θ.symm.map_smul c _)
  · exact key x

end WeilSheaf

end AlgebraicGeometry
