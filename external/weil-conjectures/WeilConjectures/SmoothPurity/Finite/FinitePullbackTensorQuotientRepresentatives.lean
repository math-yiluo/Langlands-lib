/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorOrdinaryQuotientSquare
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Quotient compatibility on flat K-flat tensor representatives

Source: Stacks Tags 06YY and 07A4, the quotient compatibility step of the
completed pullback/tensor comparison.
(blueprint: lem-pur-finite-pullback-tensor-quotient-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory finitePullbackTensorConstruction
  coefficientFiniteQuotientDerived coefficientFiniteQuotientModel
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  finiteIntrinsicDerivedTensor finiteIntrinsicClosed pullbackTensorCalculus
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local instance] sfIntrinsicPullback_additive
  coefficientFiniteQuotientExtensionAdditive

private theorem tensor_map_comp {C D : Type*} [Category* C] [Category* D]
    (T : C × C ⥤ D) {A B C' D' E' F' : C}
    (a : A ⟶ B) (b : B ⟶ C') (c : D' ⟶ E') (d : E' ⟶ F') :
    T.map (Prod.mkHom (a ≫ b) (c ≫ d)) =
      T.map (Prod.mkHom a c) ≫ T.map (Prod.mkHom b d) := by
  simpa only [CategoryTheory.prod_comp] using
    T.map_comp (Prod.mkHom a c) (Prod.mkHom b d)

private theorem tensor_map_comp_three {C D : Type*} [Category* C] [Category* D]
    (T : C × C ⥤ D) {A0 A1 A2 A3 B0 B1 B2 B3 : C}
    {a : A0 ⟶ A3} {b : B0 ⟶ B3}
    {a1 : A0 ⟶ A1} {a2 : A1 ⟶ A2} {a3 : A2 ⟶ A3}
    {b1 : B0 ⟶ B1} {b2 : B1 ⟶ B2} {b3 : B2 ⟶ B3}
    (ha : a = a1 ≫ a2 ≫ a3) (hb : b = b1 ≫ b2 ≫ b3) :
    T.map (Prod.mkHom a b) = T.map (Prod.mkHom a1 b1) ≫
      T.map (Prod.mkHom a2 b2) ≫ T.map (Prod.mkHom a3 b3) := by
  rw [ha, hb, tensor_map_comp, tensor_map_comp]

private theorem representativeKFlat_of_iso (W : Scheme.{u}) (n : ℕ)
    {P Q : CochainComplex (normalizedDVRModules l E W n) ℤ} (e : P ≅ Q)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) P) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) Q := by
  let R := integralCoefficientCommRingSheaf l E W n
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro L hL
  exact (hP L hL).of_iso
    (((MonoidalCategory.curriedTensor _).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ)).obj L |>.mapIso e)

private theorem quotientModel_naturality (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    {P Q : CochainComplex (normalizedDVRModules l E W m) ℤ}
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W m) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W m) Q) (a : P ⟶ Q) :
    (coefficientFiniteQuotientDerived l E W h).map (DerivedCategory.Q.map a) ≫
        (coefficientFiniteQuotientModel l E W h Q hQ).hom =
      (coefficientFiniteQuotientModel l E W h P hP).hom ≫
        DerivedCategory.Q.map
          (((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex (.up ℤ)).map a) := by
  have hn := (coefficientFiniteQuotientCounit l E W h).naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map a)
  have hm (K : CochainComplex (normalizedDVRModules l E W m) ℤ)
      (hK : CochainComplex.IsKFlatIndependentCoefficients
        (R := integralCoefficientCommRingSheaf l E W m) K) :
      (coefficientFiniteQuotientModel l E W h K hK).hom =
        (coefficientFiniteQuotientCounit l E W h).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj K) := by
    unfold coefficientFiniteQuotientModel coefficientLocalizedCounitModel
    change (coefficientFiniteQuotientDerived l E W h).map (𝟙 _) ≫ _ ≫ 𝟙 _ = _
    erw [(coefficientFiniteQuotientDerived l E W h).map_id, Category.id_comp, Category.comp_id]
    rfl
  rw [hm, hm]
  exact hn

private theorem tensorModel_naturality (W : Scheme.{u}) (n : ℕ)
    {P Q P' Q' : CochainComplex (normalizedDVRModules l E W n) ℤ}
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) Q)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) P')
    (hQ' : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) Q') (a : P ⟶ P') (b : Q ⟶ Q') :
    (coefficientFiniteTensorModelIso l E W
        (pullbackTensorCalculus l E W).toCoefficientDerivedSystemTensors n P Q hP hQ).hom ≫
        (finiteIntrinsicDerivedTensor l E W n).map
          (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) =
      DerivedCategory.Q.map ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).map (Prod.mkHom a b)) ≫
      (coefficientFiniteTensorModelIso l E W
        (pullbackTensorCalculus l E W).toCoefficientDerivedSystemTensors n P' Q'
          hP' hQ').hom := by
  exact ((pullbackTensorCalculus l E W).finiteTensorModel n).comparison.hom.naturality
    (Prod.mkHom
      (ObjectProperty.homMk (X := ⟨P, hP⟩) (Y := ⟨P', hP'⟩) a)
      (ObjectProperty.homMk (X := ⟨Q, hQ⟩) (Y := ⟨Q', hQ'⟩) b)) |>.symm

private theorem pullbackTensorIso_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] (n : ℕ)
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    (finitePullbackTensorConstructionIso l E f n).hom.app (M, N) =
      ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY) M N).hom := by
  unfold finitePullbackTensorConstructionIso finitePullbackTensorConstruction
  rfl

/-- Elementary pasting of the representative normalization squares. -/
private theorem representative_square_pasting {C : Type*} [Category* C]
    {A0 A1 A2 A3 A4 A5 B0 B1 B2 B3 B4 C0 C1 C2 C3 C4 C5
      D0 D1 D2 D3 D4 D5 D6 : C}
    {a : A0 ⟶ A1} {b : A1 ⟶ A2} {t : A2 ⟶ A3} {r : A3 ⟶ A4}
    {p : A4 ⟶ A5} {f : A0 ⟶ B0} {k : B0 ⟶ B1} {s : B1 ⟶ B2}
    {g : A2 ⟶ B2} {v : B2 ⟶ B3} {j : A3 ⟶ B3} {x : B3 ⟶ B4}
    {c : B4 ⟶ A5} {q : B1 ⟶ C0} {z : C0 ⟶ C1} {sn : C1 ⟶ B4}
    {q0 : B0 ⟶ C2} {w : C2 ⟶ C0} {y : C1 ⟶ C3} {sn' : C3 ⟶ A5}
    {d : C2 ⟶ C4} {vay : C4 ⟶ C5} {vkn : C5 ⟶ C3}
    {e : A1 ⟶ D0} {ty : D0 ⟶ D1} {nn : D1 ⟶ A4}
    {et : A0 ⟶ D2} {ha : D2 ⟶ D0} {hy : D1 ⟶ D3} {hq : D2 ⟶ D4}
    {hay : D4 ⟶ D5} {hs : D5 ⟶ D3} {mn : D3 ⟶ D6} {up : A4 ⟶ D6}
    {un : D6 ⟶ A5} {nt : D5 ⟶ C5} {n0 : D4 ⟶ C4}
    (hkm : a ≫ b ≫ g = f ≫ k ≫ s)
    (htnat : g ≫ v = t ≫ j) (hpost : r ≫ p = j ≫ x ≫ c)
    (hax : s ≫ v ≫ x = q ≫ z ≫ sn) (hqnat : k ≫ q = q0 ≫ w)
    (hsnat : sn ≫ c = y ≫ sn') (hchain : w ≫ z ≫ y = d ≫ vay ≫ vkn)
    (henat : a ≫ e = et ≫ ha) (hhay : ha ≫ ty ≫ hy = hq ≫ hay ≫ hs)
    (hmunat : hy ≫ mn = nn ≫ up) (hsplit : p = up ≫ un)
    (hkn : hs ≫ mn ≫ un = nt ≫ vkn ≫ sn') (hfnat : hay ≫ nt = n0 ≫ vay)
    (htot : et ≫ hq ≫ n0 = f ≫ q0 ≫ d) :
    a ≫ b ≫ t ≫ r ≫ p = a ≫ e ≫ ty ≫ nn ≫ p := by
  rw [hpost, ← reassoc_of% htnat, reassoc_of% hkm, reassoc_of% hax,
    reassoc_of% hqnat, hsnat, reassoc_of% hchain]
  rw [reassoc_of% henat, hsplit, ← reassoc_of% hmunat,
    reassoc_of% hhay, hkn, reassoc_of% hfnat, reassoc_of% htot]

attribute [local irreducible] coefficientFiniteTensorModelIso coefficientTotalTensor

-- The concrete coefficient categories require many definitional identifications.
attribute [local irreducible] sfIntrinsicPullback coefficientFiniteQuotientExtension in
/-- The quotient tensor square holds on flat-term K-flat pairs.
Source: Stacks, sites-cohomology.tex, Tag 07A4 (lemma-pullback-tensor-product),
with the derived change-of-rings construction of Tag 06YY
(blueprint: lem-pur-finite-pullback-tensor-quotient-representatives).
Proof: use the flat-term K-flat complexes P and Q to compute their derived tensor.
The ordinary unit equation hc identifies the quotient/pullback comparison on every
section inserted by both adjunction units. The degree equations hcc identify its
termwise extension on complexes. On the total summand of bidegree (i,j), both
paths carry 1 tensor f*(x tensor y) to f*(1 tensor x) tensor f*(1 tensor y).
The quotient tensor normalization gives exactly this formula for its tensorator.
Balancing, sheafification, and the total-summand inclusions determine the two
ordinary chain maps, so they agree; the signed differential is the same along
both paths. Apply the derived quotient functor. The normalized square he rewrites
all quotient/pullback components, and the quotient model counits rewrite the
remaining coefficient comparisons. Naturality cancels the intermediate model
isomorphisms, yielding the displayed square. No flatness of the coefficient
quotient is used, and the same calculation includes m=n and zero complexes.
This assertion concerns these representative pairs only; extension to arbitrary
derived objects requires a separate resolution and naturality argument. -/
theorem finitePullbackTensor_quotient_representatives {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    {m n : ℕ} (h : n ≤ m)
    (c : sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f ⋙
        coefficientFiniteQuotientExtension l E X h ≅
      coefficientFiniteQuotientExtension l E Y h ⋙
        sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
    (hc : ∀ (M : normalizedDVRModules l E Y m) (U : Y.ProEt)
        (x : M.val.obj (Opposite.op U)),
        (c.hom.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj U))
          (coefficientFiniteQuotientUnitSection l E X h
            ((sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f).obj M)
            (Opposite.op ((proEtaleBaseChange f).obj U))
            (((sfIntrinsicConstantModuleAdjunction f
              (finiteCoefficientRing l E (m + 1))).unit.app M).val.app (Opposite.op U) x)) =
        ((sfIntrinsicConstantModuleAdjunction f
          (finiteCoefficientRing l E (n + 1))).unit.app
            ((coefficientFiniteQuotientExtension l E Y h).obj M)).val.app (Opposite.op U)
          (coefficientFiniteQuotientUnitSection l E Y h M (Opposite.op U) x))
    (cc : (sfIntrinsicPullback
        (finiteCoefficientRing l E (m + 1)) f).mapHomologicalComplex (.up ℤ) ⋙
        (coefficientFiniteQuotientExtension l E X h).mapHomologicalComplex (.up ℤ) ≅
      (coefficientFiniteQuotientExtension l E Y h).mapHomologicalComplex (.up ℤ) ⋙
        (sfIntrinsicPullback
          (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex (.up ℤ))
    (hcc : ∀ (P : CochainComplex (normalizedDVRModules l E Y m) ℤ) (i : ℤ),
      (cc.hom.app P).f i = c.hom.app (P.X i))
    (good : ∀ (P : CochainComplex (normalizedDVRModules l E Y m) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (R := integralCoefficientCommRingSheaf l E Y m) P →
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (R := integralCoefficientCommRingSheaf l E X m)
        (((sfIntrinsicPullback
          (finiteCoefficientRing l E (m + 1)) f).mapHomologicalComplex (.up ℤ)).obj P))
    (e : finiteDerivedPullback l E m f ⋙ coefficientFiniteQuotientDerived l E X h ≅
      coefficientFiniteQuotientDerived l E Y h ⋙ finiteDerivedPullback l E n f)
    (he : ∀ (P : CochainComplex (normalizedDVRModules l E Y m) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (J := ProEt.topology Y) (R := integralCoefficientCommRingSheaf l E Y m) P),
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (finiteDerivedPullback l E n f).map
            (coefficientFiniteQuotientModel l E Y h P hP).hom ≫
          (sfIntrinsicPullback
            (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app _ =
        (coefficientFiniteQuotientDerived l E X h).map
          ((sfIntrinsicPullback
            (finiteCoefficientRing l E (m + 1)) f).mapDerivedCategoryFactors.hom.app P) ≫
          (coefficientFiniteQuotientModel l E X h _
            (good P hP)).hom ≫
          DerivedCategory.Q.map (cc.hom.app P))
    (P Q : CochainComplex (normalizedDVRModules l E Y m) ℤ)
    (hP : proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y m) P)
    (hQ : proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y m) Q) :
    let M := DerivedCategory.Q.obj P
    let N := DerivedCategory.Q.obj Q
    (coefficientFiniteQuotientDerived l E X h).map
      ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f m hX hY) M N).hom ≫
      ((pullbackTensorCalculus l E X).quotientCalculus.tensor h).hom.app
        ((finiteDerivedPullback l E m f).obj M,(finiteDerivedPullback l E m f).obj N) ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (e.hom.app M)
          (e.hom.app N)) =
    e.hom.app
      ((finiteIntrinsicDerivedTensor l E Y m).obj (M,N)) ≫
      (finiteDerivedPullback l E n f).map
        (((pullbackTensorCalculus l E Y).quotientCalculus.tensor h).hom.app (M,N)) ≫
      ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY)
        ((coefficientFiniteQuotientDerived l E Y h).obj M)
        ((coefficientFiniteQuotientDerived l E Y h).obj N)).hom := by
  let FY := sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f
  let HY := sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f
  let F := finiteDerivedPullback l E m f
  let H := finiteDerivedPullback l E n f
  let GX := coefficientFiniteQuotientDerived l E X h
  let GY := coefficientFiniteQuotientDerived l E Y h
  let FX := FY.mapHomologicalComplex (.up ℤ)
  let QY := (coefficientFiniteQuotientExtension l E Y h).mapHomologicalComplex (.up ℤ)
  let SX := pullbackTensorCalculus l E X
  let SY := pullbackTensorCalculus l E Y
  let TYm := coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
    (integralCoefficientCommRingSheaf l E Y m)
  have hp : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E Y m) P := hP.1
  have hq : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E Y m) Q := hQ.1
  have hgp := SY.quotientCalculus.preservesKFlat h P hp
  have hgq := SY.quotientCalculus.preservesKFlat h Q hq
  have hfp := good P hp
  have hfq := good Q hq
  have hgfp := SX.quotientCalculus.preservesKFlat h (FX.obj P) hfp
  have hgfq := SX.quotientCalculus.preservesKFlat h (FX.obj Q) hfq
  have hfgp := representativeKFlat_of_iso l E X n (cc.app P) hgfp
  have hfgq := representativeKFlat_of_iso l E X n (cc.app Q) hgfq
  obtain ⟨km, hkmgen, hkm⟩ := finitePullbackTensor_kflat_normalization l E f m
    P Q hp hq hfp hfq
  obtain ⟨kn, hkngen, hkn⟩ := finitePullbackTensor_kflat_normalization l E f n
    (QY.obj P) (QY.obj Q) hgp hgq hfgp hfgq
  obtain ⟨ax, haxgen, hax⟩ := SX.quotientCalculus.tensor_model h
    (FX.obj P) (FX.obj Q) hfp hfq
  obtain ⟨ay, haygen, hay⟩ := SY.quotientCalculus.tensor_model h P Q hp hq
  have hchain := finitePullbackTensor_ordinary_quotient_square l E f h c hc cc hcc P Q
    km kn ax ay hkmgen hkngen haxgen haygen
  let sa := coefficientFiniteTensorModelIso l E Y
    SY.toCoefficientDerivedSystemTensors m P Q hp hq
  let xp := coefficientFiniteQuotientModel l E X h (FX.obj P) hfp
  let xq := coefficientFiniteQuotientModel l E X h (FX.obj Q) hfq
  let yp := coefficientFiniteQuotientModel l E Y h P hp
  let yq := coefficientFiniteQuotientModel l E Y h Q hq
  let tf := finiteIntrinsicDerivedTensor l E X m
  let tg := finiteIntrinsicDerivedTensor l E Y n
  let tt := finiteIntrinsicDerivedTensor l E X n
  let fp := FY.mapDerivedCategoryFactors.hom.app P
  let fq := FY.mapDerivedCategoryFactors.hom.app Q
  let np := HY.mapDerivedCategoryFactors.hom.app (QY.obj P)
  let nq := HY.mapDerivedCategoryFactors.hom.app (QY.obj Q)
  let mm := (@finitePullbackTensorConstruction l _ E _ _ _ X Y f m hX hY)
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
  let nn := (@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY)
    (GY.obj (DerivedCategory.Q.obj P)) (GY.obj (DerivedCategory.Q.obj Q))
  let tx := (SX.quotientCalculus.tensor h).hom
  let ty := (SY.quotientCalculus.tensor h).hom
  dsimp only [CoefficientTensorComparisonSquare] at hax hay
  have hpaste := he P hp
  have hqpaste := he Q hq
  have hpaste' : e.hom.app (DerivedCategory.Q.obj P) ≫ H.map yp.hom ≫ np =
      GX.map fp ≫ xp.hom ≫ DerivedCategory.Q.map (cc.hom.app P) := hpaste
  have hqpaste' : e.hom.app (DerivedCategory.Q.obj Q) ≫ H.map yq.hom ≫ nq =
      GX.map fq ≫ xq.hom ≫ DerivedCategory.Q.map (cc.hom.app Q) := hqpaste
  have htnat := tx.naturality (Prod.mkHom fp fq)
  change GX.map (tf.map (Prod.mkHom fp fq)) ≫
      tx.app (DerivedCategory.Q.obj (FX.obj P), DerivedCategory.Q.obj (FX.obj Q)) =
    tx.app (F.obj (DerivedCategory.Q.obj P), F.obj (DerivedCategory.Q.obj Q)) ≫
      tt.map (Prod.mkHom (GX.map fp) (GX.map fq)) at htnat
  have hmunat := (finitePullbackTensorConstructionIso l E f n).hom.naturality
    (Prod.mkHom yp.hom yq.hom)
  simp only [pullbackTensorIso_app] at hmunat
  change H.map (tg.map (Prod.mkHom yp.hom yq.hom)) ≫
      ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY)
        (DerivedCategory.Q.obj (QY.obj P)) (DerivedCategory.Q.obj (QY.obj Q))).hom =
    nn.hom ≫ tt.map (Prod.mkHom (H.map yp.hom) (H.map yq.hom)) at hmunat
  have henat := e.hom.naturality sa.hom
  change GX.map (F.map sa.hom) ≫
      e.hom.app ((finiteIntrinsicDerivedTensor l E Y m).obj
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) =
    e.hom.app (DerivedCategory.Q.obj (TYm.obj (P, Q))) ≫ H.map (GY.map sa.hom) at henat
  have hqnat := quotientModel_naturality l E X h
    (good (TYm.obj (P, Q))
      (coefficientTotalTensor_isKFlat.{u, u + 1, u} (ProEt.topology Y)
        (integralCoefficientCommRingSheaf l E Y m) P Q hp hq))
    (coefficientTotalTensor_isKFlat.{u, u + 1, u} (ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X m) _ _ hfp hfq) km.hom
  have hsnat := tensorModel_naturality l E X n hgfp hgfq hfgp hfgq
    (cc.hom.app P) (cc.hom.app Q)
  have hfnat := HY.mapDerivedCategoryFactors.hom.naturality ay.hom
  have htot := he (TYm.obj (P, Q))
    (coefficientTotalTensor_isKFlat.{u, u + 1, u} (ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y m) P Q hp hq)
  have hpost : tt.map (Prod.mkHom
        (e.hom.app (DerivedCategory.Q.obj P) ≫ H.map yp.hom ≫ np)
        (e.hom.app (DerivedCategory.Q.obj Q) ≫ H.map yq.hom ≫ nq)) =
      tt.map (Prod.mkHom (GX.map fp) (GX.map fq)) ≫
      tt.map (Prod.mkHom xp.hom xq.hom) ≫
      tt.map (Prod.mkHom (DerivedCategory.Q.map (cc.hom.app P))
        (DerivedCategory.Q.map (cc.hom.app Q))) := by
    exact tensor_map_comp_three tt hpaste' hqpaste'
  have hkmG := congrArg GX.map hkm
  simp only [CategoryTheory.Functor.map_comp] at hkmG
  have hchainQ := congrArg DerivedCategory.Q.map hchain
  simp only [CategoryTheory.Functor.map_comp] at hchainQ
  have hhay := congrArg H.map hay
  simp only [CategoryTheory.Functor.map_comp] at hhay
  let post := tt.mapIso
    ((H.mapIso yp ≪≫ HY.mapDerivedCategoryFactors.app (QY.obj P)).prod
      (H.mapIso yq ≪≫ HY.mapDerivedCategoryFactors.app (QY.obj Q)))
  have hpost' : tt.map (Prod.mkHom (e.hom.app (DerivedCategory.Q.obj P))
        (e.hom.app (DerivedCategory.Q.obj Q))) ≫ post.hom =
      tt.map (Prod.mkHom (GX.map fp) (GX.map fq)) ≫
      tt.map (Prod.mkHom xp.hom xq.hom) ≫
      tt.map (Prod.mkHom (DerivedCategory.Q.map (cc.hom.app P))
        (DerivedCategory.Q.map (cc.hom.app Q))) := by
    change tt.map _ ≫ tt.map (Prod.mkHom (H.map yp.hom ≫ np)
      (H.map yq.hom ≫ nq)) = _
    exact (tensor_map_comp tt _ _ _ _).symm.trans hpost
  have hsplit : post.hom = tt.map (Prod.mkHom (H.map yp.hom) (H.map yq.hom)) ≫
      tt.map (Prod.mkHom np nq) := by
    change tt.map (Prod.mkHom (H.map yp.hom ≫ np) (H.map yq.hom ≫ nq)) = _
    exact tensor_map_comp tt _ _ _ _
  apply (cancel_epi (GX.map (F.map sa.hom))).1
  apply (cancel_mono post.hom).1
  change (GX.map (F.map sa.hom) ≫ GX.map mm.hom ≫ tx.app _ ≫
      tt.map (Prod.mkHom (e.hom.app (DerivedCategory.Q.obj P))
        (e.hom.app (DerivedCategory.Q.obj Q)))) ≫ post.hom =
    (GX.map (F.map sa.hom) ≫ e.hom.app _ ≫ H.map (ty.app _) ≫ nn.hom) ≫ post.hom
  simp only [Category.assoc]
  exact representative_square_pasting hkmG htnat hpost' hax hqnat hsnat hchainQ
    henat hhay hmunat hsplit hkn hfnat htot

end WeilConjectures
