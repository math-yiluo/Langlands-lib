/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefNativeOpenTensorModelsExistence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper

/-! # Open support comparisons on strict systems

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03DI and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private def transposeNatTrans {C D B : Type*}
    [Category* C] [Category* D] [Category* B] {F : D ⥤ B} {G : B ⥤ D}
    (adj : F ⊣ G) {K : C ⥤ D} {H : C ⥤ B} (t : K ⟶ H ⋙ G) : K ⋙ F ⟶ H where
  app M := (adj.homEquiv _ _).symm (t.app M)
  naturality _M _N f := adj.homEquiv_naturality_right_square _ _ _ _ (t.naturality f)

private theorem transposeNatTrans_isIso {C D B : Type*}
    [Category* C] [Category* D] [Category* B] {F : D ⥤ B} {G : B ⥤ D}
    (adj : F ⊣ G) {K : C ⥤ D} {H : C ⥤ B} (t : K ⟶ H ⋙ G)
    (ht : ∀ M, IsIso (t.app M)) (hc : ∀ M, IsIso (adj.counit.app (H.obj M))) :
    IsIso (transposeNatTrans adj t) := by
  have hi (M : C) : IsIso ((transposeNatTrans adj t).app M) := by
    have := ht M
    change IsIso (F.map (t.app M) ≫ adj.counit.app (H.obj M))
    exact IsIso.comp_isIso' (Functor.map_isIso _ _) (hc M)
  exact NatIso.isIso_of_isIso_app _

private def adjointComparisonData {C D C' D' : Type*}
    [Category* C] [Category* D] [Category* C'] [Category* D']
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} (b : L' ⊣ R')
    (I : C ⥤ C') (H : D ⥤ D') (s : H ⋙ R' ≅ R ⋙ I)
    (hu : ∀ M, IsIso (a.unit.app M))
    (hc : ∀ M, IsIso (b.counit.app (H.obj (L.obj M)))) :
    { e : L ⋙ H ≅ I ⋙ L' // ∀ M : C,
      (b.homEquiv _ _) (e.inv.app M) =
        I.map (a.unit.app M) ≫ s.inv.app (L.obj M) } := by
  let t : I ⟶ (L ⋙ H) ⋙ R' :=
    Functor.whiskerRight a.unit I ≫ Functor.whiskerLeft L s.inv
  have ht (M : C) : IsIso (t.app M) := by
    have := hu M
    change IsIso (I.map (a.unit.app M) ≫ s.inv.app (L.obj M))
    exact IsIso.comp_isIso' (Functor.map_isIso _ _) inferInstance
  let e : L ⋙ H ≅ I ⋙ L' := (@asIso _ _ _ _ (transposeNatTrans b (K := I) (H := L ⋙ H) t)
    (transposeNatTrans_isIso b (K := I) (H := L ⋙ H) t ht hc)).symm
  refine ⟨e, ?_⟩
  intro M
  exact (b.homEquiv _ _).apply_symm_apply _

private def tensorUnitSquare {C D : Type*} [Category* C] [Category* D]
    (J : C ⥤ D) (P : D ⥤ C) (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (eta : 𝟭 C ⟶ J ⋙ P) (s : TD ⋙ P ≅ P.prod P ⋙ TC) :
    (𝟭 C).prod P ⋙ TC ⟶ (J.prod (𝟭 D) ⋙ TD) ⋙ P :=
  Functor.whiskerRight (eta.prod (𝟙 P)) TC ≫
    Functor.whiskerLeft (J.prod (𝟭 D)) s.inv

private theorem tensorUnitSquare_app_isIso {C D : Type*}
    [Category* C] [Category* D]
    (J : C ⥤ D) (P : D ⥤ C) (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (eta : 𝟭 C ⟶ J ⋙ P) (s : TD ⋙ P ≅ P.prod P ⋙ TC)
    (hu : ∀ M, IsIso (eta.app M)) (MN : C × D) :
    IsIso ((tensorUnitSquare J P TC TD eta s).app MN) := by
  have := hu MN.1
  let e := Iso.prod (asIso (eta.app MN.1)) (Iso.refl (P.obj MN.2))
  change IsIso (TC.map e.hom ≫ s.inv.app (J.obj MN.1, MN.2))
  exact IsIso.comp_isIso' (TC.mapIso e).isIso_hom inferInstance

private theorem finiteUnitIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) : IsIso (finiteOpenAdj l E j n).unit := by
  let F := sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 1))
  let G := sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) j
  let a := sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1)) j
  have : F.Full := by
    dsimp [F, sfIntrinsicExtensionByZero]
    infer_instance
  have : F.Faithful := by
    dsimp [F, sfIntrinsicExtensionByZero]
    infer_instance
  have : IsIso a.unit := a.unit_isIso_of_L_fully_faithful
  let e : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ 𝟭 _ :=
    Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso (asIso a.unit).symm ≪≫
      Functor.mapDerivedCategoryIdIso _
  have ff := (finiteOpenAdj l E j n).fullyFaithfulLOfCompIsoId e
  have := ff.full
  have := ff.faithful
  exact (finiteOpenAdj l E j n).unit_isIso_of_L_fully_faithful

private theorem openUnitIso (o : Operations l E) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (M : System l E U) :
    IsIso ((o.extension j).adj.unit.app M) := by
  apply ((calculus l E U).isIso_iff_evaluations _).mpr
  intro n
  have := finiteUnitIso l E j n
  have hu := unit_mateEquiv_symm (o.extension j).adj (finiteOpenAdj l E j n)
    (pullbackTensorDerivedEvaluation l E j n).hom M
  rw [(o.openEvaluation j).transpose n] at hu
  have : IsIso ((coefficientSequenceDerivedEvaluation l E U n).map
      ((o.extension j).adj.unit.app M) ≫
        (pullbackTensorDerivedEvaluation l E j n).hom.app
          ((Operations.shriek l E o j).obj M)) := by
    rw [hu]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((pullbackTensorDerivedEvaluation l E j n).hom.app
      ((Operations.shriek l E o j).obj M))

private theorem openCounitIso_of_finiteSupport (o : Operations l E)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (N : System l E X)
    (h : ∀ n : ℕ,
      ((sfIntrinsicExtensionByZero j
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory).essImage
          ((coefficientSequenceDerivedEvaluation l E X n).obj N)) :
    IsIso ((o.extension j).adj.counit.app N) := by
  apply ((calculus l E X).isIso_iff_evaluations _).mpr
  intro n
  have := finiteUnitIso l E j n
  have ff := (finiteOpenAdj l E j n).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : IsIso ((finiteOpenAdj l E j n).counit.app
      ((coefficientSequenceDerivedEvaluation l E X n).obj N)) :=
    (finiteOpenAdj l E j n).isIso_counit_app_iff_mem_essImage.mpr (h n)
  have hc := mateEquiv_counit_symm (o.extension j).adj (finiteOpenAdj l E j n)
    (pullbackTensorDerivedEvaluation l E j n).hom N
  rw [(o.openEvaluation j).transpose n] at hc
  have : IsIso (((o.openEvaluation j).evaluation n).inv.app
      ((pull l E j).obj N) ≫
      (coefficientSequenceDerivedEvaluation l E X n).map
        ((o.extension j).adj.counit.app N)) := by
    rw [← hc]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (((o.openEvaluation j).evaluation n).inv.app ((pull l E j).obj N)) _

private theorem cartesianOpenCounitIso (o : Operations l E)
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback a j' j g) (M : System l E U) :
    IsIso ((o.extension j').adj.counit.app
      ((pull l E g).obj ((Operations.shriek l E o j).obj M))) := by
  apply openCounitIso_of_finiteSupport l E o j'
  intro n
  obtain ⟨b⟩ := proEtale_openSquareExchange l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  let e := (pullbackTensorDerivedEvaluation l E g n).app
      ((Operations.shriek l E o j).obj M) ≪≫
    (finiteDerivedPullback l E n g).mapIso (((o.openEvaluation j).evaluation n).app M) ≪≫
      (b.exchange a j' j g sq).app
        ((coefficientSequenceDerivedEvaluation l E U n).obj M)
  exact Functor.essImage.ofIso e.symm
    (((sfIntrinsicExtensionByZero j'
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory).obj_mem_essImage _)

section
attribute [local irreducible] Functor.mapDerivedCategory HasDerivedCategory.standard
  DerivedCategory _root_.instCategoryDerivedCategory
  Open.adj pullbackTensorSequenceDerived

private def betaData (o : Operations l E)
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (s : pull l E g ⋙ pull l E j' ≅ pull l E j ⋙ pull l E a)
    (sq : IsPullback a j' j g) :=
  adjointComparisonData
    (L := Operations.shriek l E o j) (R := pull l E j) (o.extension j).adj
    (L' := Operations.shriek l E o j') (R' := pull l E j') (o.extension j').adj
    (pull l E a) (pull l E g) s
    (openUnitIso l E o j) (cartesianOpenCounitIso l E o a j' j g sq)

end

attribute [local irreducible] betaData

private theorem tensorOpenCounitIso (o : Operations l E)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : System l E U) (N : System l E X) :
    IsIso ((o.extension j).adj.counit.app
      ((calculus l E X).systemClosed.tensor.obj ((Operations.shriek l E o j).obj M, N))) := by
  obtain ⟨O, On, _⟩ := CoefSupportOpenTensor.nativeOpenTensorModels_exists l E j
    (calculus l E U) (calculus l E X)
  apply openCounitIso_of_finiteSupport l E o j
  intro n
  let e := Functor.mapDerivedCategoryNatIso
    (compactSupportOpenModel j (Padic.coefficientExtensionRing l E (n + 1)))
  let M' := (coefficientSequenceDerivedEvaluation l E U n).obj M
  let N' := (coefficientSequenceDerivedEvaluation l E X n).obj N
  let t := (calculus l E X).finiteClosed n |>.tensor
  let i := ((calculus l E X).evaluationTensor n).app
      ((Operations.shriek l E o j).obj M, N) ≪≫
    t.mapIso (Iso.prod (((o.openEvaluation j).evaluation n).app M) (Iso.refl N')) ≪≫
    t.mapIso (Iso.prod (e.app M').symm (Iso.refl N')) ≪≫
    (On n).gamma.app (M', N') ≪≫ e.app _
  exact Functor.essImage.ofIso i.symm
    (((sfIntrinsicExtensionByZero j
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory).obj_mem_essImage _)

private def projectionInverse (o : Operations l E)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    openTensorRight l E o j ⟶ openTensorLeft l E o j :=
  transposeNatTrans (o.extension j).adj
    (tensorUnitSquare (Operations.shriek l E o j) (pull l E j)
      (calculus l E U).systemClosed.tensor (calculus l E X).systemClosed.tensor
      (o.extension j).adj.unit (pullbackTensorSystemComparison l E j))

private theorem projectionInverse_isIso (o : Operations l E)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (projectionInverse l E o j) := by
  unfold projectionInverse
  apply transposeNatTrans_isIso
  · exact tensorUnitSquare_app_isIso (Operations.shriek l E o j) (pull l E j)
      (calculus l E U).systemClosed.tensor (calculus l E X).systemClosed.tensor
      (o.extension j).adj.unit (pullbackTensorSystemComparison l E j)
      (openUnitIso l E o j)
  · intro MN
    exact tensorOpenCounitIso l E o j MN.1 MN.2

private def projectionComparison (o : Operations l E)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    openTensorLeft l E o j ≅ openTensorRight l E o j :=
  (@asIso _ _ _ _ (projectionInverse l E o j) (projectionInverse_isIso l E o j)).symm

private theorem projectionComparison_transpose (o : Operations l E)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : System l E U) (N : System l E X) :
    ((o.extension j).adj.homEquiv _ _)
      ((projectionComparison l E o j).inv.app (M, N)) =
      (calculus l E U).systemClosed.tensor.map
        (Prod.mkHom ((o.extension j).adj.unit.app M) (𝟙 ((pull l E j).obj N))) ≫
      (pullbackTensorSystemComparison l E j).inv.app
        ((Operations.shriek l E o j).obj M, N) :=
  (o.extension j).adj.homEquiv _ _ |>.apply_symm_apply _

private def finiteClopenIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j] (n : ℕ) :
    (sfIntrinsicExtensionByZero j
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory ≅
    proEtaleConstantDerivedDirectImage j (Padic.coefficientExtensionRing l E (n + 1)) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let eU := sfIntrinsicModuleEquivalence U A
  let eX := sfIntrinsicModuleEquivalence X A
  let F := sfIntrinsicExtensionByZero j A
  let D := proEtaleConstantModuleDirectImage j A
  have := ProEtale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j j.isClosedEmbedding.isClosed_range
  let e : F ≅ D :=
    Functor.isoWhiskerLeft eU.inverse
      (Functor.isoWhiskerRight
        (asIso (ProEtale.openImmersionLowerShriekToLowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)) eX.functor ≪≫
        (sfIntrinsicDirectImageComparison j A).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eU.counitIso D ≪≫ Functor.leftUnitor D
  have : PreservesFiniteLimits D := preservesFiniteLimits_of_natIso e
  have : PreservesFiniteColimits D := preservesFiniteColimits_of_natIso e
  let a := SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    (sfIntrinsicConstantModuleAdjunction j A)
  exact Functor.mapDerivedCategoryNatIso e ≪≫
    a.rightAdjointUniq (finiteAdj l E j n)

private theorem finiteClopenUnitIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j] (n : ℕ)
    (M : proEtaleDerivedCategory U (Padic.coefficientExtensionRing l E (n + 1))) :
    IsIso ((finiteAdj l E j n).unit.app
      (((sfIntrinsicExtensionByZero j
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory).obj M)) := by
  have := finiteUnitIso l E j n
  let ff := (finiteOpenAdj l E j n).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : (proEtaleConstantDerivedDirectImage j
      (Padic.coefficientExtensionRing l E (n + 1))).Full :=
    Functor.Full.of_iso (finiteClopenIso l E j n)
  have : (proEtaleConstantDerivedDirectImage j
      (Padic.coefficientExtensionRing l E (n + 1))).Faithful :=
    Functor.Faithful.of_iso (finiteClopenIso l E j n)
  exact (finiteAdj l E j n).isIso_unit_app_of_iso ((finiteClopenIso l E j n).app M)

private theorem clopenDirectUnitIso (o : Operations l E) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j] (M : System l E U) :
    IsIso ((o.direct j).adj.unit.app ((Operations.shriek l E o j).obj M)) := by
  apply ((calculus l E X).isIso_iff_evaluations _).mpr
  intro n
  have := finiteClopenUnitIso l E j n
    ((coefficientSequenceDerivedEvaluation l E U n).obj M)
  have hu : IsIso ((finiteAdj l E j n).unit.app
      ((coefficientSequenceDerivedEvaluation l E X n).obj
        ((Operations.shriek l E o j).obj M))) :=
    (NatTrans.isIso_app_iff_of_iso (finiteAdj l E j n).unit
      (((o.openEvaluation j).evaluation n).app M)).mpr
      (finiteClopenUnitIso l E j n
        ((coefficientSequenceDerivedEvaluation l E U n).obj M))
  have he := (o.evaluation j).unit n ((Operations.shriek l E o j).obj M)
  have : IsIso ((coefficientSequenceDerivedEvaluation l E X n).map
      ((o.direct j).adj.unit.app ((Operations.shriek l E o j).obj M)) ≫
      ((o.evaluation j).evaluation n).hom.app
        ((pull l E j).obj ((Operations.shriek l E o j).obj M)) ≫
      (proEtaleConstantDerivedDirectImage j
        (Padic.coefficientExtensionRing l E (n + 1))).map
          ((pullbackTensorDerivedEvaluation l E j n).hom.app
            ((Operations.shriek l E o j).obj M))) := by
    rw [he]
    exact hu
  exact IsIso.of_isIso_comp_right _
    (((o.evaluation j).evaluation n).hom.app
      ((pull l E j).obj ((Operations.shriek l E o j).obj M)) ≫
      (proEtaleConstantDerivedDirectImage j
        (Padic.coefficientExtensionRing l E (n + 1))).map
          ((pullbackTensorDerivedEvaluation l E j n).hom.app
            ((Operations.shriek l E o j).obj M)))

private def clopenComparison (o : Operations l E) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j] :
    Operations.shriek l E o j ≅ Operations.push l E o j := by
  have hi := openUnitIso l E o j
  let eta : 𝟭 (System l E U) ≅ Operations.shriek l E o j ⋙ pull l E j :=
    NatIso.ofComponents (fun M ↦ @asIso _ _ _ _ ((o.extension j).adj.unit.app M) (hi M))
      (fun f ↦ (o.extension j).adj.unit.naturality f)
  let b := Functor.whiskerLeft (Operations.shriek l E o j) (o.direct j).adj.unit
  have hb (M : System l E U) : IsIso (b.app M) := clopenDirectUnitIso l E o j M
  have : IsIso b := NatIso.isIso_of_isIso_app _
  exact (Functor.rightUnitor _).symm ≪≫ asIso b ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight eta.symm (Operations.push l E o j) ≪≫ Functor.leftUnitor _

private theorem clopenComparison_transpose (o : Operations l E) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j] (M : System l E U) :
    (clopenComparison l E o j).hom.app M =
      ((o.direct j).adj.homEquiv _ _)
        (@inv _ _ _ _ ((o.extension j).adj.unit.app M) (openUnitIso l E o j M)) := by
  simp only [clopenComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, asIso_hom,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    NatIso.ofComponents_inv_app, asIso_inv,
    Functor.leftUnitor_hom_app, Category.id_comp,
    Adjunction.homEquiv_unit]
  erw [Category.comp_id]

/-- Open support comparisons for the fixed section-normalized system compositors.
Source: Stacks 03DI, 09AE, 0E8I; blueprint fix-prop-coherence, slice comparisons
(blueprint: lem-sf-integral-system-open-comparisons).

Proof: the finite open extension is fully faithful; exact localization retains
its invertible unit. The normalized open evaluation mate carries the system unit
to a composite of this finite unit with isomorphisms. Joint conservativity of
finite evaluation makes the system unit invertible. The same mate identity for
counits detects membership in the essential image of system open extension
from membership at every finite level.
Finite cartesian open exchange shows that pullback of an extended object has
this support. Transpose the prescribed pullback of the system unit followed by
c.square.inv. It is a composite of isomorphisms after the target open counit,
so is invertible. Naturality of the transpose gives the base-change isomorphism
and its exact required inverse-transpose equation. No identification between
c.square and a separately chosen base-change map is needed.
For tensor support, use the existing native finite open tensor models for the
fixed calculi. Their gamma isomorphisms, the adjunction-normalized comparison
from native to intrinsic open extension, and evaluationTensor show that tensor
of an extended system with any system has the same open support. Transpose the
specified tensor of the open unit followed by pullbackTensorSystemComparison.inv.
The open counit and this transpose are invertible, yielding the natural projection
isomorphism with precisely the requested inverse-transpose equation.
For clopen j, transport the existing ordinary extension/direct-image isomorphism
through the canonical intrinsic realizations. Both functors are then exact;
uniqueness of right adjoints identifies exact localization of direct image with
its recorded universal right derivation. Finite evaluation of the system direct
unit at an extended object is therefore invertible. Its composite with direct
image of the inverse open unit gives the clopen comparison and the stated
transpose. All uses of evaluation detect invertibility, never equality. Empty
opens, identity immersions and zero complexes require no separate assumptions. -/
theorem integralSystemOpenComparisons (o : Operations l E) (c : Compositors l E o) :
    Nonempty (OpenComparisons l E o c) := by
  exact ⟨{
    unitIso := fun j _ M ↦ openUnitIso l E o j M
    beta := fun a j' j g _ _ h sq ↦ (betaData l E o a j' j g (c.square l E a j' j g h) sq).val
    beta_transpose := fun a j' j g _ _ h sq M ↦
      (betaData l E o a j' j g (c.square l E a j' j g h) sq).property M
    projection := fun j _ ↦ projectionComparison l E o j
    projection_transpose := fun j _ M N ↦ projectionComparison_transpose l E o j M N
    clopen := fun j _ _ ↦ clopenComparison l E o j
    clopen_transpose := fun j _ _ M ↦ clopenComparison_transpose l E o j M }⟩

end WeilConjectures.IntegralSystemRealization
