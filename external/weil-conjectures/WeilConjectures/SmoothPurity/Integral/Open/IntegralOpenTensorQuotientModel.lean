/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Open.IntegralOpenTensorRepresentative
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SmoothPurity.Integral.Open.IntegralOpenScalarRestrictionComparison
import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionQuotientModel
import WeilConjectures.SmoothPurity.Integral.Open.IntegralOpenTensorModuleQuotientSquare

/-! # The scalar quotient square on explicit open tensor models

Source: Stacks Tags 0E8I, 0GL1, 06YY and 0941; the strict-model normalization in
`lem-sf-integral-open-reduction-comparison`
(blueprint: lem-sf-integral-open-tensor-quotient-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian

universe t u c v r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

attribute [local instance 3000] SheafOfModules.instCategory SheafOfModules.instPreadditive

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  coefficientFiniteReductionModel integralOpenTensorChainIso scalarReductionExtension

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X V : Scheme.{t}} (j : X ⟶ V) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)

private instance restrictionZero (T : Scheme.{t}) (n : ℕ) :
    (normalizedDVRModuleRes l E T (Nat.le_succ n)).PreservesZeroMorphisms := by
  let := normalizedDVRModuleRes_additive l E T (Nat.le_succ n)
  infer_instance

section ExactSquares

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [K.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits K] [PreservesFiniteColimits K]

private theorem squareFactors (e : F ⋙ G ≅ H ⋙ K) (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
        K.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app P) ≫
        K.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj P) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F G).inv.app
    (DerivedCategory.Q.obj P))).mp
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [Category.assoc]
  erw [Functor.mapDerivedCategoryCompIso_hom_app_factors]
  simp only [Iso.inv_hom_id_app_assoc]
  erw [Functor.mapDerivedCategoryNatIso_fac,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  rfl

private theorem localize_square (e : F ⋙ G ≅ H ⋙ K)
    {xm : CochainComplex B ℤ} {xn : CochainComplex A ℤ}
    {vm : CochainComplex D ℤ} {vn : CochainComplex C ℤ}
    (tx : xm ⟶ (F.mapHomologicalComplex (.up ℤ)).obj xn)
    (tv : vm ⟶ (K.mapHomologicalComplex (.up ℤ)).obj vn)
    (bm : vm ≅ (G.mapHomologicalComplex (.up ℤ)).obj xm)
    (bn : vn ≅ (H.mapHomologicalComplex (.up ℤ)).obj xn)
    (hs : tv ≫ (K.mapHomologicalComplex (.up ℤ)).map bn.hom =
      bm.hom ≫ (G.mapHomologicalComplex (.up ℤ)).map tx ≫
        (NatIso.mapHomologicalComplex e (.up ℤ)).hom.app xn) :
    (DerivedCategory.Q.map tv ≫ K.mapDerivedCategoryFactors.inv.app vn) ≫
        K.mapDerivedCategory.map
          (DerivedCategory.Q.map bn.hom ≫ H.mapDerivedCategoryFactors.inv.app xn) =
      (DerivedCategory.Q.map bm.hom ≫ G.mapDerivedCategoryFactors.inv.app xm) ≫
        G.mapDerivedCategory.map
          (DerivedCategory.Q.map tx ≫ F.mapDerivedCategoryFactors.inv.app xn) ≫
        (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj xn) := by
  apply (cancel_mono (K.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app xn) ≫
    K.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj xn))).mp
  have hk : K.mapDerivedCategory.map
        (DerivedCategory.Q.map bn.hom ≫ H.mapDerivedCategoryFactors.inv.app xn) ≫
      K.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app xn) =
        K.mapDerivedCategory.map (DerivedCategory.Q.map bn.hom) := by
    rw [← K.mapDerivedCategory.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  have hg : G.mapDerivedCategory.map
        (DerivedCategory.Q.map tx ≫ F.mapDerivedCategoryFactors.inv.app xn) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app xn) =
        G.mapDerivedCategory.map (DerivedCategory.Q.map tx) := by
    rw [← G.mapDerivedCategory.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  have hkn := K.mapDerivedCategoryFactors.hom.naturality bn.hom
  have hgn := G.mapDerivedCategoryFactors.hom.naturality tx
  dsimp only [Functor.comp_map] at hkn hgn
  simp only [Category.assoc]
  erw [reassoc_of% hk, squareFactors F G H K e xn, reassoc_of% hg]
  erw [hkn, reassoc_of% hgn]
  simp only [Iso.inv_hom_id_app_assoc]
  have hq := congrArg DerivedCategory.Q.map hs
  erw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp] at hq
  exact hq

end ExactSquares

private theorem reassocSix {T : Type*} [Category T]
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : T}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₄)
    (e : A₄ ⟶ A₅) (f : A₅ ⟶ A₆) :
    a ≫ b ≫ c ≫ (d ≫ e) ≫ f = a ≫ b ≫ c ≫ d ≫ e ≫ f := by
  simp only [Category.assoc]

private theorem reassocSeven {T : Type*} [Category T]
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : T}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₄)
    (e : A₄ ⟶ A₅) (f : A₅ ⟶ A₆) (g : A₆ ⟶ A₇) :
    a ≫ b ≫ ((c ≫ d) ≫ e) ≫ f ≫ g = a ≫ b ≫ c ≫ (d ≫ e) ≫ f ≫ g := by
  simp only [Category.assoc]

private theorem conjugate_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (R : C ⥤ D) (S : A ⥤ B) (J : B ⥤ D) (L : A ⥤ C)
    (e : S ⋙ J ≅ L ⋙ R)
    {v₀ v₁ : D} {v₀' v₁' : C} {x₀ x₁ : B} {x₀' x₁' : A}
    (dv : v₀ ⟶ R.obj v₀') (dx : x₀ ⟶ S.obj x₀')
    (tv : v₁ ⟶ R.obj v₁') (tx : x₁ ⟶ S.obj x₁')
    (av : v₀ ≅ v₁) (av' : v₀' ≅ v₁') (ax : x₀ ≅ x₁) (ax' : x₀' ≅ x₁')
    (b : v₁ ⟶ J.obj x₁) (b' : v₁' ⟶ L.obj x₁')
    (hv : dv ≫ R.map av'.hom = av.hom ≫ tv)
    (hx : dx ≫ S.map ax'.hom = ax.hom ≫ tx)
    (hs : tv ≫ R.map b' = b ≫ J.map tx ≫ e.hom.app x₁') :
    dv ≫ R.map (av'.hom ≫ b' ≫ L.map ax'.inv) =
      (av.hom ≫ b ≫ J.map ax.inv) ≫ J.map dx ≫ e.hom.app x₀' := by
  have hx' : tx ≫ S.map ax'.inv = ax.inv ≫ dx := by
    apply (cancel_epi ax.hom).mp
    rw [← Category.assoc, ← hx]
    simp only [Category.assoc, ← S.map_comp, Iso.hom_inv_id, S.map_id,
      Category.comp_id, Iso.hom_inv_id_assoc]
  have he := e.hom.naturality ax'.inv
  dsimp only [Functor.comp_map] at he
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← Category.assoc dv, hv, Category.assoc, reassoc_of% hs]
  rw [← he, ← J.map_comp_assoc, hx', J.map_comp]
  simp only [Category.assoc]

/-- The generator-normalized open scalar square and the scalar-unit quotient square
on flat tensor models, before any strict-system comparison is chosen.
Source: Stacks 0E8I, 0GL1, 06YY and 0941; parent proof Steps 1--3.
(blueprint: lem-sf-integral-open-tensor-quotient-model).

Proof: Naturality of o.systemMap on each horizontal coefficient arrow, together
with o.systemComponents, gives the commutative square of the finite transport ring
maps and the two quotient maps. Concrete continuous module pushforward composes
with scalar restriction by the identity on sections, so this square gives the
finite transport isomorphism. Compose it with the inverse of RingedOpenScalar's
extension/scalar comparison to construct ordinary. Its summand-generator formula,
and the identity on transported sections, prove the displayed HEq of functions.
To check the ordinary open tensor quotient square, transpose under scalar
extension/restriction and test on the scalar-unit image of each extension summand.
Both composites send a section x to the same section at the smaller coefficient
level, by tensor.generators and the defining scalar-adjunction units. The tensor
Hom equivalence and the extension/sheafification Hom equivalence then identify the
maps. Apply this equality degreewise to Q. The canonical K-flat finite-reduction
model identifies the localization of the ordinary quotient transformation with
integralOpenReductionStep: transpose the localized scalar unit, using the specified
derived scalar-adjunction normalization and the successive-restriction comparison.
Apply the exact-localization composition identities to the finite extensions and
the two scalar restrictions; these are exactly mapDerivedCategorySquareIso ordinary.
Cancel the finite-reduction model isomorphisms. This gives the displayed square for
the explicitly constructed tensor representative iso. No reduction calculus, complete
object, or choice of strict open comparison is involved. Empty sums and zero terms
satisfy the same equations, n=0 denotes exponent one, and K-flatness, not boundedness
or quotient-flatness, justifies the reduction model. -/
theorem integralOpenTensorQuotientModel
    (tensor : IntegralOpenReduction.TensorComparison l E j o) :
    ∃ ordinary : ∀ n : ℕ,
      normalizedDVRModuleRes l E X (Nat.le_succ n) ⋙
          IntegralOpenReduction.finiteExtension l E j o (n + 1) ≅
        IntegralOpenReduction.finiteExtension l E j o n ⋙
          normalizedDVRModuleRes l E V (Nat.le_succ n),
      (∀ (n : ℕ) (M : normalizedDVRModules l E X n) (W : V.ProEt)
        (a : W ⟶ IntegralOpenReduction.openObject j),
        HEq (fun x : ((normalizedDVRModuleRes l E X (Nat.le_succ n)).obj M).val.obj
            (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) ↦
          ((ordinary n).hom.app M).val.app (op W)
            (IntegralOpenReduction.finiteExtensionSection l E j o (n + 1)
              ((normalizedDVRModuleRes l E X (Nat.le_succ n)).obj M) W a x))
          (fun x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) ↦
            IntegralOpenReduction.finiteExtensionSection l E j o n M W a x)) ∧
      let openRestriction (n : ℕ) :
          normalizedDVRRes l E X (Nat.le_succ n) ⋙
              compactSupportCanonicalJLevel l E j o (n + 1) ≅
            compactSupportCanonicalJLevel l E j o n ⋙
              normalizedDVRRes l E V (Nat.le_succ n) := by
        -- Supply the witnesses over the recorded standard categories directly.
        exact @Functor.mapDerivedCategorySquareIso
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (normalizedDVRModuleRes_additive l E X (Nat.le_succ n))
          (normalizedDVRModuleRes_limits l E X (Nat.le_succ n))
          (normalizedDVRModuleRes_colimits l E X (Nat.le_succ n))
          (IntegralOpenReduction.finiteExtensionAdditive l E j o (n + 1))
          (compactSupportFiniteExtensionPreservesFiniteLimits l E j o (n + 1))
          (compactSupportFiniteExtensionPreservesFiniteColimits l E j o (n + 1))
          (IntegralOpenReduction.finiteExtensionAdditive l E j o n)
          (compactSupportFiniteExtensionPreservesFiniteLimits l E j o n)
          (compactSupportFiniteExtensionPreservesFiniteColimits l E j o n)
          (normalizedDVRModuleRes_additive l E V (Nat.le_succ n))
          (normalizedDVRModuleRes_limits l E V (Nat.le_succ n))
          (normalizedDVRModuleRes_colimits l E V (Nat.le_succ n))
          (ordinary n)
      ∀ (Q : CochainComplex (scalarReductionSource l E X) ℤ)
        (hQ : CochainComplex.IsKFlatIndependentCoefficients
          (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) Q)
        (hJQ : CochainComplex.IsKFlatIndependentCoefficients
          (J := ProEt.topology V) (R := completedIntegralCommRingSheafUnrestricted l E V)
          (((IntegralOpenReduction.extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q))
        (n : ℕ),
      (integralOpenReductionStep l E V n).app
          ((IntegralOpenReduction.shriek l E j o).obj (DerivedCategory.Q.obj Q)) ≫
        (normalizedDVRRes l E V (Nat.le_succ n)).map
          (integralOpenTensorRepresentativeIso l E j o tensor Q hQ hJQ n).hom =
      (integralOpenTensorRepresentativeIso l E j o tensor Q hQ hJQ (n + 1)).hom ≫
        (compactSupportCanonicalJLevel l E j o (n + 1)).map
          ((integralOpenReductionStep l E X n).app (DerivedCategory.Q.obj Q)) ≫
        (openRestriction n).hom.app
          ((coefficientFiniteDerivedExtension l E X n).obj (DerivedCategory.Q.obj Q)) := by
  classical
  choose ordinary hgen using integralOpenScalarRestrictionComparison l E j o
  refine ⟨ordinary, hgen, ?_⟩
  dsimp only
  intro Q hQ hJQ n
  let R := normalizedDVRModuleRes l E V (Nat.le_succ n)
  let S := normalizedDVRModuleRes l E X (Nat.le_succ n)
  let Jm : normalizedDVRModules l E X (n + 1) ⥤ normalizedDVRModules l E V (n + 1) :=
    IntegralOpenReduction.finiteExtension l E j o (n + 1)
  let Jn : normalizedDVRModules l E X n ⥤ normalizedDVRModules l E V n :=
    IntegralOpenReduction.finiteExtension l E j o n
  have : PreservesFiniteLimits Jm :=
    compactSupportFiniteExtensionPreservesFiniteLimits l E j o (n + 1)
  have : PreservesFiniteColimits Jm :=
    compactSupportFiniteExtensionPreservesFiniteColimits l E j o (n + 1)
  have : PreservesFiniteLimits Jn := compactSupportFiniteExtensionPreservesFiniteLimits l E j o n
  have : PreservesFiniteColimits Jn :=
    compactSupportFiniteExtensionPreservesFiniteColimits l E j o n
  have : PreservesFiniteLimits R := normalizedDVRModuleRes_limits l E V (Nat.le_succ n)
  have : PreservesFiniteColimits R := normalizedDVRModuleRes_colimits l E V (Nat.le_succ n)
  have : PreservesFiniteLimits S := normalizedDVRModuleRes_limits l E X (Nat.le_succ n)
  have : PreservesFiniteColimits S := normalizedDVRModuleRes_colimits l E X (Nat.le_succ n)
  have : R.Additive := normalizedDVRModuleRes_additive l E V (Nat.le_succ n)
  have : S.Additive := normalizedDVRModuleRes_additive l E X (Nat.le_succ n)
  have : Jm.Additive := IntegralOpenReduction.finiteExtensionAdditive l E j o (n + 1)
  have : Jn.Additive := IntegralOpenReduction.finiteExtensionAdditive l E j o n
  have : R.PreservesZeroMorphisms := by infer_instance
  have : S.PreservesZeroMorphisms := by infer_instance
  have : Jm.PreservesZeroMorphisms := by infer_instance
  have : Jn.PreservesZeroMorphisms := by infer_instance
  let : (S ⋙ Jm).PreservesZeroMorphisms := Functor.preservesZeroMorphisms_comp S Jm
  let : (Jn ⋙ R).PreservesZeroMorphisms := Functor.preservesZeroMorphisms_comp Jn R
  let en : S ⋙ Jm ≅ Jn ⋙ R := ordinary n
  let JQ : CochainComplex (scalarReductionSource l E V) ℤ :=
    ((IntegralOpenReduction.extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q
  let PX (k : ℕ) := ((scalarReductionExtension l E X k).mapHomologicalComplex (.up ℤ)).obj Q
  let PV (k : ℕ) := ((scalarReductionExtension l E V k).mapHomologicalComplex (.up ℤ)).obj JQ
  let tx : PX (n + 1) ⟶ (S.mapHomologicalComplex (.up ℤ)).obj (PX n) :=
    (NatTrans.mapHomologicalComplex
    (coefficientOrdinaryQuotient l E X (Nat.le_succ n)) (.up ℤ)).app Q
  let tv : PV (n + 1) ⟶ (R.mapHomologicalComplex (.up ℤ)).obj (PV n) :=
    (NatTrans.mapHomologicalComplex
    (coefficientOrdinaryQuotient l E V (Nat.le_succ n)) (.up ℤ)).app JQ
  let dx := (integralOpenReductionStep l E X n).app (DerivedCategory.Q.obj Q)
  let dv := (integralOpenReductionStep l E V n).app
    ((IntegralOpenReduction.shriek l E j o).obj (DerivedCategory.Q.obj Q))
  let txd := DerivedCategory.Q.map tx ≫ S.mapDerivedCategoryFactors.inv.app (PX n)
  let tvd := DerivedCategory.Q.map tv ≫ R.mapDerivedCategoryFactors.inv.app (PV n)
  let ax (k : ℕ) := coefficientFiniteReductionModel l E X Q hQ k
  let av (k : ℕ) :=
    (coefficientFiniteDerivedExtension l E V k).mapIso
        ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.app Q) ≪≫
      coefficientFiniteReductionModel l E V JQ hJQ k
  let b (k : ℕ) :=
    let := compactSupportFiniteExtensionPreservesFiniteLimits l E j o k
    let := compactSupportFiniteExtensionPreservesFiniteColimits l E j o k
    DerivedCategory.Q.map (integralOpenTensorChainIso l E j o tensor Q k).hom ≫
      (IntegralOpenReduction.finiteExtension l E j o k).mapDerivedCategoryFactors.inv.app (PX k)
  have hx : dx ≫ S.mapDerivedCategory.map (ax n).hom = (ax (n + 1)).hom ≫ txd := by
    apply (cancel_mono (S.mapDerivedCategoryFactors.hom.app (PX n))).mp
    dsimp only [txd]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app, Category.comp_id]
    exact integralReductionQuotientModel l E X Q hQ n
  have hv' : (integralOpenReductionStep l E V n).app (DerivedCategory.Q.obj JQ) ≫
      R.mapDerivedCategory.map (coefficientFiniteReductionModel l E V JQ hJQ n).hom =
        (coefficientFiniteReductionModel l E V JQ hJQ (n + 1)).hom ≫ tvd := by
    apply (cancel_mono (R.mapDerivedCategoryFactors.hom.app (PV n))).mp
    dsimp only [tvd]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app, Category.comp_id]
    exact integralReductionQuotientModel l E V JQ hJQ n
  have hv : dv ≫ R.mapDerivedCategory.map (av n).hom = (av (n + 1)).hom ≫ tvd := by
    dsimp only [av, Iso.trans_hom, Functor.mapIso_hom]
    rw [R.mapDerivedCategory.map_comp, ← Category.assoc]
    change ((integralOpenReductionStep l E V n).app _ ≫
      (normalizedDVRRes l E V (Nat.le_succ n)).map
        ((coefficientFiniteDerivedExtension l E V n).map
          ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.hom.app Q))) ≫
        _ = _
    have hn := (integralOpenReductionStep l E V n).naturality
      ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.hom.app Q)
    simp only [Functor.comp_map] at hn
    rw [← hn]
    rw [Category.assoc]
    erw [hv']
    exact (Category.assoc
      ((coefficientFiniteDerivedExtension l E V (n + 1)).map
        ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.hom.app Q))
      (coefficientFiniteReductionModel l E V JQ hJQ (n + 1)).hom tvd).symm
  have hs : tv ≫ (R.mapHomologicalComplex (.up ℤ)).map
        (integralOpenTensorChainIso l E j o tensor Q n).hom =
      (integralOpenTensorChainIso l E j o tensor Q (n + 1)).hom ≫
        (Jm.mapHomologicalComplex (.up ℤ)).map tx ≫
        (NatIso.mapHomologicalComplex en (.up ℤ)).hom.app (PX n) := by
    apply HomologicalComplex.hom_ext
    intro i
    simp only [tv, tx, NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex,
      integralOpenTensorChainIso, HomologicalComplex.Hom.isoOfComponents]
    exact integralOpenTensorModuleQuotientSquare l E j o tensor n (ordinary n) (hgen n) (Q.X i)
  -- Pass the degreewise module square through exact localization.
  have hlocal := localize_square S Jm Jn R en tx tv
    (integralOpenTensorChainIso l E j o tensor Q (n + 1))
    (integralOpenTensorChainIso l E j o tensor Q n) hs
  have h := conjugate_square R.mapDerivedCategory S.mapDerivedCategory
    Jm.mapDerivedCategory Jn.mapDerivedCategory (Functor.mapDerivedCategorySquareIso en)
    dv dx tvd txd (av (n + 1)) (av n) (ax (n + 1)) (ax n)
    (b (n + 1)) (b n) hv hx hlocal
  dsimp only [integralOpenTensorRepresentativeIso, av, ax, b, Iso.trans, Iso.symm,
    Functor.mapIso] at h ⊢
  dsimp only [R, S, Jn, Jm, normalizedDVRRes, compactSupportCanonicalJLevel] at h ⊢
  simp only [Functor.map_comp, Category.assoc] at h ⊢
  erw [R.mapDerivedCategory.map_comp, R.mapDerivedCategory.map_comp] at h
  erw [R.mapDerivedCategory.map_comp]
  have hl := reassocSix dv
    (R.mapDerivedCategory.map ((coefficientFiniteDerivedExtension l E V n).map
      ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.app Q).hom))
    (R.mapDerivedCategory.map (coefficientFiniteReductionModel l E V JQ hJQ n).hom)
    (R.mapDerivedCategory.map
      (DerivedCategory.Q.map (integralOpenTensorChainIso l E j o tensor Q n).hom))
    (R.mapDerivedCategory.map (Jn.mapDerivedCategoryFactors.inv.app (PX n)))
    (R.mapDerivedCategory.map
      (Jn.mapDerivedCategory.map (coefficientFiniteReductionModel l E X Q hQ n).inv))
  exact hl.symm.trans (h.trans (reassocSeven
    ((coefficientFiniteDerivedExtension l E V (n + 1)).map
      ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.app Q).hom)
    (coefficientFiniteReductionModel l E V JQ hJQ (n + 1)).hom
    (DerivedCategory.Q.map (integralOpenTensorChainIso l E j o tensor Q (n + 1)).hom)
    (Jm.mapDerivedCategoryFactors.inv.app (PX (n + 1)))
    (Jm.mapDerivedCategory.map (coefficientFiniteReductionModel l E X Q hQ (n + 1)).inv)
    (Jm.mapDerivedCategory.map dx)
    ((Functor.mapDerivedCategorySquareIso en).hom.app
      ((coefficientFiniteDerivedExtension l E X n).obj (DerivedCategory.Q.obj Q)))))

end WeilConjectures
