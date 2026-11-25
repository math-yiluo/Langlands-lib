/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedForgetTwoInjective.StandardBifunctorHomModel
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.Algebra.Homology.BifunctorHomCone
import WeilConjectures.Algebra.Homology.BifunctorHomComplex
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Derived representatives for the underlying continuous-coefficient Hom

Source: Stacks Tags 0A95 and 08J7.
(blueprint: lem-sf-underlying-standard-hom-representatives)
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedForgetTwoInjective
open MonoidalCategory MonObj

namespace UnderlyingHomAux
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]
open Mod
/-- The quotient map defining the relative tensor product is linear in its first factor. -/
private noncomputable def relativeTensorπ (M N : Mod C R) :
    (Mod.tensorRight R N.X).obj M ⟶ M ⊗ N :=
  homMk (M := (Mod.tensorRight R N.X).obj M) (N := M ⊗ N) (tensorObjπ M N) (by
    change ((α_ R M.X N.X).inv ≫ γ[R,M.X] ▷ N.X) ≫ tensorObjπ M N =
      R ◁ tensorObjπ M N ≫ γ[R,(M ⊗ N).X]
    simpa only [Category.assoc] using (whiskerLeft_tensorπ_smul M N).symm)

/-- The relative tensor product is a cofork of the two action maps on module objects. -/
private noncomputable def relativeTensorCofork (M N : Mod C R) :
    Cofork ((tensorRightMap R γ[R,N.X]).app M)
      ((tensorRightRightAct R N.X).app M) :=
  Cofork.ofπ (relativeTensorπ M N) (by
    apply Mod.hom_ext
    change M.X ◁ γ[R,N.X] ≫ tensorObjπ M N =
      ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X) ≫ tensorObjπ M N
    rw [Category.assoc, tensorObjπ_condition]
    simp only [Category.assoc, Iso.inv_hom_id_assoc])

/-- The tensor cofork is a coequalizer, as can be checked after forgetting the module action. -/
private noncomputable def isColimitRelativeTensorCofork (M N : Mod C R) :
    IsColimit (relativeTensorCofork M N) := by
  apply isColimitOfIsColimitCoforkMap (forget R)
  change IsColimit (Cofork.ofπ (tensorObjπ M N) _ :
    Cofork (M.X ◁ γ[R,N.X]) ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X))
  refine Cofork.IsColimit.mk _
    (fun s ↦ coequalizer.desc (f := rightAct M ▷ N.X)
      (g := (α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) s.π ?_) ?_ ?_
  · have h := s.condition
    change M.X ◁ γ[R,N.X] ≫ s.π =
      ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X) ≫ s.π at h
    rw [← cancel_epi (α_ M.X R N.X).inv]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm
  · intro s
    exact coequalizer.π_desc _ _
  · intro s m hm
    apply coequalizer.hom_ext (f := rightAct M ▷ N.X)
      (g := (α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X])
    exact hm.trans (coequalizer.π_desc _ _).symm

private noncomputable def tensorComponent (M N : Mod C R) :
    (Mod.tensorLeft N).obj M ≅ M ⊗ N :=
  HasColimit.isoOfNatIso
    (diagramIsoParallelPair ((Mod.tensorLeftDiagram R N).flip.obj M)) ≪≫
      (colimit.isColimit _).coconePointUniqueUpToIso
        (isColimitRelativeTensorCofork M N)

omit [MonoidalPreadditive C] in
private lemma tensorComponent_π (M N : Mod C R) :
    Mod.tensorπ M N ≫ (tensorComponent M N).hom.hom = Mod.tensorObjπ M N := by
  have h := congrArg Mod.Hom.hom
    (show colimit.ι ((Mod.tensorLeftDiagram R N).flip.obj M) WalkingParallelPair.one ≫
        (tensorComponent M N).hom = relativeTensorπ M N by
      simp [tensorComponent, HasColimit.ι_isoOfNatIso_hom_assoc, relativeTensorCofork])
  exact h

private noncomputable def tensorIso (N : Mod C R) :
    Mod.tensorLeft N ≅ MonoidalCategory.tensorRight N :=
  NatIso.ofComponents (fun M ↦ tensorComponent M N) (by
    intro M M' f
    apply Mod.tensorLeft_obj_hom_ext
    simp only [Mod.comp_hom', Mod.tensorπ_map_assoc]
    rw [tensorComponent_π, ← Category.assoc, tensorComponent_π]
    exact (Mod.tensorObjπ_whiskerRight f).symm)

private instance tensorAdditive (M : Mod C R) : (Mod.tensorLeft M).Additive :=
  (Mod.ihomAdjunction M).left_adjoint_additive

private lemma uncurry_add {P M N : Mod C R} (a b : P ⟶ (Mod.ihom M).obj N) :
    Mod.uncurryHom (a + b) = Mod.uncurryHom a + Mod.uncurryHom b := by
  simp only [Mod.uncurryHom, Mod.add_hom, MonoidalPreadditive.add_whiskerRight,
    Preadditive.add_comp]

private noncomputable def transposeAdd (P M N : Mod C R) :
    (P ⟶ (Mod.ihom M).obj N) ≃+ (M ⟶ (Mod.ihom P).obj N) :=
  { Mod.transposeEquiv with
    map_add' := by
      intro a b
      apply Mod.uncurryHom_injective
      change Mod.uncurryHom (Mod.transpose (a + b)) =
        Mod.uncurryHom (Mod.transpose a + Mod.transpose b)
      rw [uncurry_add, Mod.uncurryHom_transpose, Mod.uncurryHom_transpose,
        Mod.uncurryHom_transpose, uncurry_add, Preadditive.comp_add] }

private noncomputable def homEquiv (P M N : Mod C R) :
    (P ⟶ (Mod.ihom M).obj N) ≃+ ((Mod.tensorLeft P).obj M ⟶ N) :=
  (transposeAdd P M N).trans ((Mod.ihomAdjunction P).homAddEquiv M N).symm

private noncomputable def H : (Mod C R)ᵒᵖ ⥤ Mod C R ⥤ Mod C R where
  obj M := Mod.ihom M.unop
  map a := Mod.ihomMap a.unop
  map_id M := Mod.ihomMap_id M.unop
  map_comp a b := Mod.ihomMap_comp b.unop a.unop

private instance : (H (R := R)).Additive :=
  ⟨fun {_M _N} a b ↦ Mod.ihomMap_add a.unop b.unop⟩

private instance (M : (Mod C R)ᵒᵖ) : ((H (R := R)).obj M).Additive :=
  inferInstanceAs (Mod.ihom M.unop).Additive

private lemma homEquiv_right (P M N N' : Mod C R)
    (φ : P ⟶ (Mod.ihom M).obj N) (g : N ⟶ N') :
    homEquiv P M N' (φ ≫ (Mod.ihom M).map g) = homEquiv P M N φ ≫ g := by
  dsimp only [homEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  change ((Mod.ihomAdjunction P).homEquiv M N').symm
      (Mod.transpose (φ ≫ (Mod.ihom M).map g)) = _
  rw [Mod.transpose_comp_ihom_map]
  exact (Mod.ihomAdjunction P).homEquiv_naturality_right_symm _ _

private lemma homEquiv_left (P M M' N : Mod C R)
    (φ : P ⟶ (Mod.ihom M).obj N) (a : M' ⟶ M) :
    homEquiv P M' N (φ ≫ (Mod.ihomMap a).app N) =
      (Mod.tensorLeft P).map a ≫ homEquiv P M N φ := by
  change ((Mod.ihomAdjunction P).homEquiv M' N).symm
      (Mod.transpose (φ ≫ (Mod.ihomMap a).app N)) = _
  rw [Mod.transpose_comp_ihomMap]
  exact (Mod.ihomAdjunction P).homEquiv_naturality_left_symm _ _

private lemma acyclic_of_lifts {D : Type*} [Category D] [Abelian D]
    (P : D) (hP : IsSeparator P) (K : CochainComplex D ℤ)
    (hlift : ∀ (n : ℤ) (φ : P ⟶ K.X n), φ ≫ K.d n (n + 1) = 0 →
      ∃ ψ : P ⟶ K.X (n - 1), ψ ≫ K.d (n - 1) n = φ) : K.Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff' K (n - 1) n (n + 1) (by simp) (by simp),
    ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
  apply hP.def
  intro t
  obtain ⟨ψ, hψ⟩ := hlift n (t ≫ kernel.ι (K.d n (n + 1))) (by simp)
  change t ≫ kernel.ι (K.d n (n + 1)) ≫ cokernel.π (K.d (n - 1) n) = t ≫ 0
  rw [← Category.assoc, ← hψ]
  simp

private lemma ordinaryAcyclic [Abelian.HasFunctorialFlatResolution (Mod C R)]
    (K I : CochainComplex (Mod C R) ℤ)
    (hK : K.Acyclic) [I.IsKInjective] :
    (CochainComplex.bifunctorHomObj H K I).Acyclic := by
  obtain ⟨P, hP, hflat⟩ :=
    Abelian.exists_flat_separator_of_hasFunctorialFlatResolution (Mod C R)
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight P) :=
    hflat.tensorRight.preservesFiniteLimits
  have : PreservesFiniteLimits (Mod.tensorLeft P) :=
    preservesFiniteLimits_of_natIso (tensorIso P).symm
  have : (Mod.tensorLeft P).IsLeftAdjoint := (Mod.ihomAdjunction P).isLeftAdjoint
  have hT : (((Mod.tensorLeft P).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
    intro n
    change ((K.sc n).map (Mod.tensorLeft P)).Exact
    exact (hK n).map (Mod.tensorLeft P)
  apply acyclic_of_lifts P hP
  intro n φ hφ
  exact CochainComplex.BifunctorHom.exists_comp_d_eq P (Mod.tensorLeft P)
    (homEquiv P) (homEquiv_right P) (homEquiv_left P) n (n - 1) (by omega)
    (fun z hz ↦ CochainComplex.HomComplex.exists_δ_eq_of_isKInjective hT z hz
      (n - 1) (by omega)) φ hφ

private lemma ordinaryQuasiIso [Abelian.HasFunctorialFlatResolution (Mod C R)]
    {K L I : CochainComplex (Mod C R) ℤ}
    (a : K ⟶ L) [QuasiIso a] [I.IsKInjective] :
    QuasiIso (CochainComplex.bifunctorHomMapLeft (H := H) (Y := I) a) := by
  let θ := (CochainComplex.exists_signedBifunctorConeIso (H (R := R)) I).choose
  have hc := ordinaryAcyclic (CochainComplex.mappingCone a) I
    ((CochainComplex.mappingCone.quasiIso_iff_acyclic a).1 inferInstance)
  have hs := HomologicalComplex.Acyclic.of_iso hc (θ K L a)
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hs ⊢
  have ht := (HomotopyCategory.subcategoryAcyclic (Mod C R)).prop_of_iso
    (((HomotopyCategory.quotient (Mod C R) (.up ℤ)).commShiftIso (-1)).app _) hs
  exact ((HomotopyCategory.subcategoryAcyclic (Mod C R)).prop_shift_iff_of_isStableUnderShift
    _ (-1 : ℤ)).1 ht

private noncomputable def rightHomotopy
    {K I I' : CochainComplex (Mod C R) ℤ} {f g : I ⟶ I'} (h : Homotopy f g) :
    Homotopy (CochainComplex.bifunctorHomMapRight (H := H) (K := K) f)
      (CochainComplex.bifunctorHomMapRight (H := H) (K := K) g) where
  hom n m := CochainComplex.bifunctorHomLift H K I' m fun p q hpq ↦
    p.negOnePow • (CochainComplex.bifunctorHomπ H K I n p (p + n) rfl ≫
      (H.obj (op (K.X p))).map (h.hom (p + n) q))
  zero n m hnm := by
    apply CochainComplex.bifunctorHomObj_hom_ext
    intro p q hpq
    simp only [CochainComplex.bifunctorHomLift_π, zero_comp]
    rw [h.zero _ _ (by simp only [ComplexShape.up_Rel] at hnm ⊢; omega)]
    simp
  comm n := by
    apply CochainComplex.bifunctorHomObj_hom_ext
    intro p q hpq
    rw [dNext_eq _ (by simp : (ComplexShape.up ℤ).Rel n (n + 1)),
      prevD_eq _ (by simp : (ComplexShape.up ℤ).Rel (n - 1) n)]
    simp only [Preadditive.add_comp, Category.assoc,
      CochainComplex.bifunctorHomMapRight_f_π, CochainComplex.bifunctorHomLift_π]
    rw [CochainComplex.bifunctorHomObj_d_π H K I' (n - 1) n p q hpq
      (p + (n - 1)) (p + 1) rfl (by omega)]
    simp only [Linear.comp_units_smul, CochainComplex.bifunctorHomLift_π_assoc,
      Preadditive.comp_sub, Linear.units_smul_comp, Category.assoc]
    rw [CochainComplex.bifunctorHomObj_d_π_assoc H K I n (n + 1) p (p + (n + 1))
      rfl (p + n) (p + 1) rfl (by omega)]
    simp only [Linear.units_smul_comp, Preadditive.sub_comp, Category.assoc,
      smul_smul, Int.units_mul_self, one_smul, Int.negOnePow_succ, Units.neg_smul,
      smul_sub, sub_neg_eq_add]
    subst q
    simp only [smul_add, smul_smul, Int.units_mul_self, one_smul]
    have hm (t : ℤ) (ht : p + 1 + n = t) :
        CochainComplex.bifunctorHomπ H K I n (p + 1) t ht ≫
            (H.map (K.d p (p + 1)).op).app (I.X t) ≫
              (H.obj (op (K.X p))).map (h.hom t (p + n)) =
          CochainComplex.bifunctorHomπ H K I n (p + 1) (p + 1 + n) rfl ≫
            (H.obj (op (K.X (p + 1)))).map (h.hom (p + 1 + n) (p + n)) ≫
              (H.map (K.d p (p + 1)).op).app (I'.X (p + n)) := by
      subst t
      rw [NatTrans.naturality]
    rw [hm (p + (n + 1)) (by omega)]
    have hh := h.comm (p + n)
    rw [dNext_eq _ (by simp only [ComplexShape.up_Rel]; omega :
        (ComplexShape.up ℤ).Rel (p + n) (p + (n + 1))),
      prevD_eq _ (by simp only [ComplexShape.up_Rel]; omega :
        (ComplexShape.up ℤ).Rel (p + (n - 1)) (p + n))] at hh
    rw [hh]
    simp only [Functor.map_add, Functor.map_comp, Preadditive.comp_add]
    abel

private lemma ordinaryQuasiIsoRight
    {K I I' : CochainComplex (Mod C R) ℤ} (g : I ⟶ I')
    [I.IsKInjective] [I'.IsKInjective] [QuasiIso g] :
    QuasiIso (CochainComplex.bifunctorHomMapRight (H := H) (K := K) g) := by
  obtain ⟨e, rfl⟩ := (CochainComplex.IsKInjective.quasiIso_iff g).mp inferInstance
  apply homotopyEquivalences_le_quasiIso _ _
  refine ⟨{ hom := CochainComplex.bifunctorHomMapRight e.hom
            inv := CochainComplex.bifunctorHomMapRight e.inv
            homotopyHomInvId := ?_
            homotopyInvHomId := ?_ }, rfl⟩
  · simpa only [CochainComplex.bifunctorHomMapRight_comp,
      CochainComplex.bifunctorHomMapRight_id] using rightHomotopy (K := K) e.homotopyHomInvId
  · simpa only [CochainComplex.bifunctorHomMapRight_comp,
      CochainComplex.bifunctorHomMapRight_id] using rightHomotopy (K := K) e.homotopyInvHomId

end UnderlyingHomAux

attribute [local instance] Sheaf.symmetricCategory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The underlying continuous-coefficient internal Hom is additive in the source.
Source: Mod.ihomMap_add (blueprint: lem-sf-underlying-standard-hom-representatives). -/
instance underlyingHomBifunctor_additive :
    (underlyingHomBifunctor (k₀ := k₀) (l := l) (X := X)).Additive :=
  ⟨by
    intro P Q f g
    exact Mod.ihomMap_add f.unop g.unop⟩

/-- The underlying continuous-coefficient internal Hom is additive in the target.
Source: Mod.ihom (blueprint: lem-sf-underlying-standard-hom-representatives). -/
instance underlyingHomBifunctor_obj_additive
    (P : (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)ᵒᵖ) :
    ((underlyingHomBifunctor (k₀ := k₀) (l := l) (X := X)).obj P).Additive :=
  inferInstanceAs (Mod.ihom P.unop).Additive

set_option linter.unusedSectionVars false in
/-- The explicitly specified underlying standard Hom complex computes a derived bifunctor,
with naturality and replacement invariance for every source and every K-injective target.
The representative equations determine this universal derived extension up to a unique
compatible natural isomorphism; no arbitrary module object is being chosen.
Source: Stacks 0A95, lemma-RHom-well-defined, and 08J7, section-internal-hom.
(blueprint: lem-sf-underlying-standard-hom-representatives).
Proof: the ordinary continuous-coefficient module category is Grothendieck abelian and has
functorial K-injective resolutions. Apply the native product-total Hom to an arbitrary source
and the canonical K-injective replacement of the target, then localize at quasi-isomorphisms
in both variables. For a K-injective target, source quasi-isomorphisms are inverted by the
usual sheaf internal-Hom acyclicity argument: choose a flat separator, transpose its maps
into the Hom complex to cochains into the K-injective target, and use acyclicity of the
source tensor the flat separator. Apply this to the mapping cone. Target quasi-isomorphisms
between K-injectives are homotopy equivalences, which Hom preserves. Thus this is a universal
derived extension. For a K-injective I, invert the image of its augmentation I → I_res and
compose with the localization factorization to obtain ρ.iso. Naturality of the augmentation
gives ρ.naturality in both variables. The two preceding invariance arguments, applied to
f and g, give ρ.inverts. Rescaling each degree-n, source-p projection by (-1)^(np) changes
neither the underlying complex nor its functorial maps, so these representatives are exactly
those of standardHomModel. The construction applies also to zero or acyclic sources. -/
theorem underlyingStandardHomRepresentatives :
    ∃ H : (DerivedCategory (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))ᵒᵖ ×
        DerivedCategory (ProEtale.AdicSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⥤
        DerivedCategory (ProEtale.AdicSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber),
      Nonempty (Representatives
        (standardHomModel (underlyingHomBifunctor (k₀ := k₀) (l := l) (X := X))).complex H) :=
  by
  classical
  let A := ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let I := CochainComplex.kInjectiveResolutionFunctor.{u + 1} A
  let aug := CochainComplex.toKInjectiveResolution.{u + 1} A
  let HC := nativeHomComplex (underlyingHomBifunctor (k₀ := k₀) (l := l) (X := X))
  let F := (𝟭 _).prod I ⋙ HC ⋙ DerivedCategory.Q.{u + 1}
  have hinv : ((HomologicalComplex.quasiIso A (.up ℤ)).op.prod
      (HomologicalComplex.quasiIso A (.up ℤ))).IsInvertedBy F := by
    intro P P' f hf
    have : QuasiIso f.1.unop := hf.1
    have : QuasiIso f.2 := hf.2
    have : QuasiIso (aug.app P.2) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} A P.2).2
    have : QuasiIso (aug.app P'.2) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} A P'.2).2
    have : (I.obj P.2).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u + 1} A P.2
    have : (I.obj P'.2).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u + 1} A P'.2
    have ht : QuasiIso (aug.app P.2 ≫ I.map f.2) := by
      rw [← aug.naturality f.2]
      dsimp
      infer_instance
    have : QuasiIso (I.map f.2) := (quasiIso_iff_comp_left _ _).mp ht
    change IsIso (DerivedCategory.Q.{u + 1}.map
      (HC.map (X := (P.1, I.obj P.2)) (Y := (P'.1, I.obj P'.2))
        (f.1, I.map f.2)))
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso A _).mpr
    have := UnderlyingHomAux.ordinaryQuasiIso (I := I.obj P.2) f.1.unop
    have := UnderlyingHomAux.ordinaryQuasiIsoRight (K := P'.1.unop) (I.map f.2)
    change QuasiIso (CochainComplex.bifunctorHomMapLeft
      (H := underlyingHomBifunctor (k₀ := k₀) (l := l) (X := X)) f.1.unop ≫
      CochainComplex.bifunctorHomMapRight (I.map f.2))
    infer_instance
  let DH : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ DerivedCategory A :=
    Localization.lift F hinv (DerivedCategory.Q.{u + 1}.op.prod DerivedCategory.Q.{u + 1})
  let e : (DerivedCategory.Q.{u + 1}.op.prod DerivedCategory.Q.{u + 1}) ⋙ DH ≅ F :=
    Localization.fac F hinv (DerivedCategory.Q.{u + 1}.op.prod DerivedCategory.Q.{u + 1})
  let α : HC ⋙ DerivedCategory.Q.{u + 1} ⟶
      (DerivedCategory.Q.{u + 1}.op.prod DerivedCategory.Q.{u + 1}) ⋙ DH :=
    Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 _)) aug) (HC ⋙ DerivedCategory.Q.{u + 1}) ≫ e.inv
  have hα (K J : CochainComplex A ℤ) [J.IsKInjective] :
      IsIso (α.app (op K, J)) := by
    have : (I.obj J).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u + 1} A J
    have : QuasiIso (aug.app J) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} A J).2
    have hq := UnderlyingHomAux.ordinaryQuasiIsoRight (K := K) (I := J)
      (I' := I.obj J) (aug.app J)
    have : IsIso (DerivedCategory.Q.{u + 1}.map (CochainComplex.bifunctorHomMapRight
        (H := underlyingHomBifunctor (k₀ := k₀) (l := l) (X := X)) (K := K)
        (aug.app J))) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hq
    dsimp [α, HC, nativeHomComplex]
    rw [CochainComplex.bifunctorHomMapLeft_id, Category.id_comp]
    infer_instance
  refine ⟨DH, ?_⟩
  change Nonempty (Representatives HC DH)
  refine ⟨{ iso := fun K J ↦ (asIso (α.app (op K, J))).symm
            naturality := ?_
            inverts := ?_ }⟩
  · intro K K' J J' _ _ f g
    apply (cancel_mono (α.app (op K', J'))).1
    simp only [Category.assoc, Iso.symm_hom, asIso_inv, IsIso.inv_hom_id,
      Category.comp_id]
    have hn := α.naturality (X := (op K, J)) (Y := (op K', J')) (f.op, g)
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.op_map] at hn
    rw [hn, IsIso.inv_hom_id_assoc]
    rfl
  · intro K K' J J' _ _ f g _ _
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    have := UnderlyingHomAux.ordinaryQuasiIso (I := J) f
    have := UnderlyingHomAux.ordinaryQuasiIsoRight (K := K') g
    change QuasiIso (CochainComplex.bifunctorHomMapLeft
      (H := underlyingHomBifunctor (k₀ := k₀) (l := l) (X := X)) f ≫
      CochainComplex.bifunctorHomMapRight g)
    infer_instance

end AlgebraicGeometry.ProEtaleWeilSheaf
