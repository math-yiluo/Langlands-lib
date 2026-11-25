/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedForgetful
public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorOperations
public import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRestrictionTensor
import WeilConjectures.WeilSheaf.Category
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatForget
import WeilConjectures.WeilSheaf.Native.NativeNormalizedTensorModels
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilUnderivedTensor
import WeilConjectures.WeilSheaf.Native.NativeHomEvaluationSquareAllSources
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorChain
import all WeilConjectures.WeilSheaf.Native.NativeClosedTransposition
import all WeilConjectures.CategoryTheory.K.KFlatBifunctorTensorHom
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRepresentativeUncurry

/-! # Forgetting the evaluation-normalized binary tensor model

Source: Stacks Project, sites-cohomology.tex, Tags 0A96 and 08J9; the fixed native
signed model comparison (blueprint: lem-sf-native-forget-normalized-binary-models).

The comparison `c` below is specified on every balanced tensor summand. These equations
uniquely determine the chain isomorphism, so the existential records the canonical
comparison and its normalization together, without choosing unrelated tensor data.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison

universe u a b

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

private theorem closedTensorIso_uncurry
    {C : Type a} [Category.{b} C] {H : Cᵒᵖ × C ⥤ C}
    (S T : WeilConjectures.CoefficientClosedStructure H) (A K L : C)
    (f : A ⟶ H.obj (op K, L)) :
    (nativeOrdinaryClosedTensorIso S T).hom.app (A, K) ≫
        (T.transpose A K L).symm f = (S.transpose A K L).symm f := by
  let a := (S.adjunction K).ofNatIsoLeft
    (nativeOrdinaryTensorSliceIso S.monoidal K).symm
  let b := (T.adjunction K).ofNatIsoLeft
    (nativeOrdinaryTensorSliceIso T.monoidal K).symm
  have ha : (a.homEquiv A L).symm f = (S.transpose A K L).symm f := by
    rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply]
    exact Category.id_comp _
  have hb : (b.homEquiv A L).symm f = (T.transpose A K L).symm f := by
    rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply]
    exact Category.id_comp _
  change (a.leftAdjointUniq b).hom.app A ≫ (T.transpose A K L).symm f = _
  rw [← ha, ← hb]
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
    ← Category.assoc, ← (a.leftAdjointUniq b).hom.naturality f,
    Category.assoc]
  exact congrArg (fun z ↦ (Prod.sectL C K ⋙ S.tensor).map f ≫ z)
    (a.leftAdjointUniq_hom_app_counit b L)

private theorem map_normalization
    {B D E : Type a} [Category.{b} B] [Category.{b} D] [Category.{b} E]
    (Q : B ⥤ D) (F : D ⥤ E) (V : B ⥤ E) (δ : Q ⋙ F ≅ V)
    {A : D} {N I : B} (m : A ⟶ Q.obj N) (j : N ⟶ I) (f : A ⟶ Q.obj I)
    (h : m ≫ Q.map j = f) :
    F.map m ≫ δ.hom.app N ≫ V.map j ≫ δ.inv.app I = F.map f := by
  have hn := δ.hom.naturality j
  change F.map (Q.map j) ≫ δ.hom.app I = δ.hom.app N ≫ V.map j at hn
  rw [← reassoc_of% hn]
  simp only [Iso.hom_inv_id_app, CategoryTheory.Functor.comp_obj,
    Category.comp_id, ← F.map_comp, h]

-- Forgetting a signed exchange uses only additivity and the summand equation.
private theorem forgotten_flip_summand
    {A B : Type a} [Category.{b} A] [Category.{b} B]
    [Abelian A] [HasCountableCoproducts A] [Preadditive B]
    (U : A ⥤ B) [U.Additive] (F : A ⥤ A ⥤ A)
    [F.Additive] [∀ A, (F.obj A).Additive]
    (P T : CochainComplex A ℤ) {Z : CochainComplex B ℤ}
    (c : (U.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor T P F) ⟶ Z)
    (p q n : ℤ) (hpq : p + q = n)
    (x : U.obj ((F.obj (T.X q)).obj (P.X p)) ⟶ Z.X n)
    (hc : U.map (HomologicalComplex.ιMapBifunctor T P F (.up ℤ) q p n
      (by change q + p = n; omega)) ≫ c.f n = x) :
    U.map (HomologicalComplex.ιMapBifunctor P T F.flip (.up ℤ) p q n hpq) ≫
      ((U.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorFlipIso T P F (.up ℤ)).hom ≫ c).f n =
      (q * p).negOnePow • x := by
  dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  rw [← U.map_comp_assoc, HomologicalComplex.ι_mapBifunctorFlipIso_hom]
  simp only [Units.smul_def, Functor.map_zsmul, Preadditive.zsmul_comp, hc]
  rfl

private theorem signed_summand_comp
    {C : Type a} [Category.{b} C] [Preadditive C] {A B D E G : C}
    (π : A ⟶ B) (i : B ⟶ D) (v : D ⟶ E) (κ : E ⟶ G)
    (j : B ⟶ E) (out : A ⟶ G) (s : ℤˣ) (hs : s * s = 1)
    (hi : i ≫ v = s • j) (hκ : π ≫ j ≫ κ = s • out) :
    π ≫ i ≫ v ≫ κ = out := by
  rw [← Category.assoc i, hi]
  have hk := congrArg (s • ·) hκ
  simp only [smul_smul, hs, one_smul] at hk
  simpa only [Units.smul_def, Preadditive.comp_zsmul, Preadditive.zsmul_comp] using hk

private theorem signed_uncurry_summand
    {C D : Type a} [Category.{b} C] [Category.{b} D] [Preadditive C] [Preadditive D]
    (U : C ⥤ D) [U.Additive] {A B T : C} {B' : D}
    (i : A ⟶ B) (v : U.obj B ⟶ B') (g : B ⟶ T)
    (i' : U.obj A ⟶ B') (g' : B' ⟶ U.obj T)
    (a : A ⟶ T) (a' : U.obj A ⟶ U.obj T) (s : ℤˣ)
    (hi : U.map i ≫ v = s • i') (hg : i ≫ g = s • a)
    (hg' : i' ≫ g' = a') (hu : U.map a = a') :
    U.map i ≫ U.map g = U.map i ≫ v ≫ g' := by
  rw [← Category.assoc, hi, Linear.units_smul_comp, hg',
    ← U.map_comp, hg, Functor.map_units_smul, hu]

-- Paste the representative square before specializing to derived categories.
private theorem representative_hom_square
    {B D E : Type a} [Category.{b} B] [Category.{b} D] [Category.{b} E]
    (Q : B ⥤ D) (V : B ⥤ E) (F : D ⥤ E) (δ : Q ⋙ F ≅ V)
    (H : Eᵒᵖ × E ⥤ E) (P T I J : B) {A : D} {J' : E}
    (e : A ≅ Q.obj J) (e' : H.obj (op (V.obj T), V.obj I) ≅ J')
    (c : V.obj J ⟶ J')
    (x : F.obj A ⟶ H.obj (op (F.obj (Q.obj T)), F.obj (Q.obj I)))
    (hs : x ≫ H.map (Prod.mkHom (δ.inv.app T).op (δ.hom.app I)) ≫ e'.hom =
      F.map e.hom ≫ δ.hom.app J ≫ c) (φ : P ⟶ J) :
    F.map (Q.map φ ≫ e.inv) ≫ x = δ.hom.app P ≫
      (V.map φ ≫ c ≫ e'.inv) ≫ H.map (Prod.mkHom (δ.hom.app T).op (δ.inv.app I)) := by
  have hm := TensorEvaluationFormal.remove_model_natural Q V F δ e e' c
    (x ≫ H.map (Prod.mkHom (δ.inv.app T).op (δ.hom.app I)))
    (by simpa only [Category.assoc] using hs) φ
  simpa only [Category.assoc, Iso.app_hom, Iso.app_inv] using
    TensorEvaluationFormal.invert_hom_square H (δ.app T) (δ.app I)
      (F.map (Q.map φ ≫ e.inv) ≫ x) (δ.hom.app P ≫ V.map φ ≫ c ≫ e'.inv)
      (by simpa only [Category.assoc, Iso.app_hom, Iso.app_inv] using hm)

-- The cancellation argument only uses the normalization squares and an adjunction.
private theorem normalized_model_forget
    {B D E : Type a} [Category.{b} B] [Category.{b} D] [Category.{b} E]
    {H : Eᵒᵖ × E ⥤ E} (T S : WeilConjectures.CoefficientClosedStructure H)
    (Q : B ⥤ D) (V : B ⥤ E) (F : D ⥤ E) (δ : Q ⋙ F ≅ V)
    (P K I N : B) {A : D} {Z : E}
    (t : F.obj A ≅ T.tensor.obj (F.obj (Q.obj P), F.obj (Q.obj K)))
    (m : A ⟶ Q.obj N) (j : N ⟶ I) (f : A ⟶ Q.obj I)
    (v : V.obj N ⟶ Z) (ψ : Z ⟶ V.obj I) [Mono ψ]
    (model : S.tensor.obj (V.obj P, V.obj K) ⟶ Z)
    (f' : V.obj P ⟶ H.obj (op (V.obj K), V.obj I))
    (hloc : m ≫ Q.map j = f)
    (hloc' : model ≫ ψ = (S.transpose (V.obj P) (V.obj K) (V.obj I)).symm f')
    (hchain : V.map j = v ≫ ψ)
    (hunc : (T.transpose (F.obj (Q.obj P)) (F.obj (Q.obj K))
        (F.obj (Q.obj I))).symm
          (δ.hom.app P ≫ f' ≫ H.map (Prod.mkHom (δ.hom.app K).op (δ.inv.app I))) =
        t.inv ≫ F.map f) :
    F.map m ≫ δ.hom.app N ≫ v = t.hom ≫
      (nativeOrdinaryClosedTensorIso T S).hom.app (F.obj (Q.obj P), F.obj (Q.obj K)) ≫
        S.tensor.map (Prod.mkHom (δ.hom.app P) (δ.hom.app K)) ≫ model := by
  apply (cancel_mono ψ).mp
  apply (cancel_mono (δ.inv.app I)).mp
  simp only [Category.assoc]
  have hleft : F.map m ≫ δ.hom.app N ≫ v ≫ ψ ≫ δ.inv.app I = F.map f := by
    rw [← Category.assoc v, ← hchain]
    exact map_normalization Q F V δ m j f hloc
  rw [hleft]
  have hun := congrArg (t.hom ≫ ·) hunc
  simp only [Iso.hom_inv_id_assoc] at hun
  rw [← hun, ← closedTensorIso_uncurry T S]
  rw [TensorEvaluationFormal.uncurry_transport S, ← hloc']
  simp only [Category.assoc]

-- Prove the signed inverse-transposition identity with abstract categories, so
-- the summand rewrites do not reduce the native sheaf and localization instances.
private theorem signed_normalization_uncurry
    {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] [HasCountableCoproducts A]
    {F : A ⥤ A ⥤ A} {H : Aᵒᵖ ⥤ A ⥤ A}
    [F.Additive] [∀ A, (F.obj A).Additive]
    [F.flip.Additive] [∀ A, (F.flip.obj A).Additive]
    [H.Additive] [∀ A, (H.obj A).Additive]
    (adj : F ⊣₂ H) (P T I : CochainComplex A ℤ)
    (j ψ : CochainComplex.mapBifunctor P T F.flip ⟶ I)
    (hψ : ∀ (p q n : ℤ) (hpq : p + q = n),
      HomologicalComplex.ιMapBifunctor P T F.flip (.up ℤ) p q n hpq ≫ ψ.f n =
        (p * q).negOnePow • ((F.obj (T.X q)).map
          ((DerivedNativeTensorProof.internalHomEquiv adj T I P
            ((HomologicalComplex.mapBifunctorFlipIso T P F (.up ℤ)).inv ≫ j)).f p ≫
              CochainComplex.bifunctorHomπ H T I p q n (by omega)) ≫
                (adj.adj (T.X q)).counit.app (I.X n))) : ψ = j := by
  let θ := (HomologicalComplex.mapBifunctorFlipIso T P F (.up ℤ)).inv ≫ j
  have hθ : (HomologicalComplex.mapBifunctorFlipIso T P F (.up ℤ)).hom ≫ θ = j := by
    simp [θ]
  rw [← hθ]
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  have hqp : q + p = n := by omega
  have hu := DerivedNativeTensorProof.internalHomEquiv_f_π adj θ p q n hqp
  have hv := congrArg ((adj.adj (T.X q)).homEquiv (P.X p) (I.X n)).symm hu
  simp only [DerivedNativeTensorProof.curry, Adjunction.homAddEquiv_apply,
    Equiv.symm_apply_apply] at hv
  rw [hψ p q n hpq]
  simp only [HomologicalComplex.comp_f, ← Category.assoc]
  rw [HomologicalComplex.ι_mapBifunctorFlipIso_hom,
    Linear.units_smul_comp, ← hv, Adjunction.homEquiv_counit]
  change (p * q).negOnePow • _ = (q * p).negOnePow • _
  rw [mul_comm q p]

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]

-- Apply the signed normalization once to an arbitrary map into a K-injective complex.
private theorem native_normalized_uncurry_map
    (P T I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeIsKFlat k₀ l X P) (hT : NativeIsKFlat k₀ l X T) (hI : I.IsKInjective)
    (j : ((nativeTensorTotal k₀ l X).obj P).obj T ⟶ I) :
    ∃ φ : P ⟶ CochainComplex.bifunctorHomObj (ihomBifunctor k₀ l X) T I,
      (∀ (p q n : ℤ) (hpq : p + q = n),
        HomologicalComplex.ιMapBifunctor P T (nativeTensorBifunctor k₀ l X).flip
          (.up ℤ) p q n hpq ≫ j.f n =
          (p * q).negOnePow • (((nativeTensorBifunctor k₀ l X).obj (T.X q)).map
            (φ.f p ≫ CochainComplex.bifunctorHomπ (ihomBifunctor k₀ l X)
              T I p q n (by omega)) ≫
                (tensorIhomAdjunction k₀ l X (T.X q)).counit.app (I.X n))) ∧
      (nativeOpenTensorModel k₀ l X P T hP hT).hom ≫ DerivedCategory.Q.map j =
        ((nativeDerivedClosedComparison k₀ l X).weilClosed.transpose
          (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj T) (DerivedCategory.Q.obj I)).symm
          (DerivedCategory.Q.map φ ≫
            ((nativeDerivedClosedComparison k₀ l X).homModels.weilRepresentatives.model
              T I hI).inv) := by
  classical
  let : (nativeTensorBifunctor k₀ l X).Additive := by
    constructor
    intro A B f g
    apply NatTrans.ext
    funext Q
    exact ((nativeTensorBifunctor k₀ l X).flip.obj Q).map_add
  let : ∀ P : ProEtaleWeilSheaf k₀ l X,
      ((nativeTensorBifunctor k₀ l X).obj P).Additive := by
    intro P
    exact (tensorIhomAdjunction k₀ l X P).left_adjoint_additive
  let a : nativeTensorBifunctor k₀ l X ⊣₂ ihomBifunctor k₀ l X :=
    { adj := tensorIhomAdjunction k₀ l X
      unit_whiskerRight_map := by
        intro A B f
        apply NatTrans.ext
        funext Q
        exact (unit_conjugateEquiv_symm (tensorIhomAdjunction k₀ l X B)
          (tensorIhomAdjunction k₀ l X A)
          ((ihomBifunctor k₀ l X).map f.op) Q).symm }
  let θ := (HomologicalComplex.mapBifunctorFlipIso T P
    (nativeTensorBifunctor k₀ l X) (.up ℤ)).inv ≫ j
  let φ := DerivedNativeTensorProof.internalHomEquiv a T I P θ
  obtain ⟨ψ, hψ, hloc⟩ := (native_normalized_tensor_models k₀ l X).choose_spec.2
    P T I hP hT hI φ
  have hψj : ψ = j := signed_normalization_uncurry a P T I j ψ hψ
  subst ψ
  exact ⟨φ, hψ, hloc⟩

-- The fixed representative squares involve several nested localization functors.
/-- The fixed native tensor model forgets to the canonical ordinary localization tensorator.
The first conjunct specifies the canonical total comparison on all balanced summands;
the second is the asserted equality with the fixed tensor-forgetting comparison.

Source: Stacks Project, sites-cohomology.tex, Tags 0A96 and 08J9, K-flat/K-injective
transposition, with the native signed normalization.
(blueprint: lem-sf-native-forget-normalized-binary-models).

Proof:
1. The native category is Grothendieck abelian by
lem-sf-native-weil-constructible-abelian. Its countable products exist by
lem-coef-grothendieck-small-limits. Choose a K-injective resolution j of the actual
native total using prose-03-02. Both forgotten inputs are K-flat
by lem-sf-native-two-sided-kflat-forget, without any termwise-flatness hypothesis.
2. The parametrized adjunction in def-sf-native-derived-tensor-layer and the chain-map
bijection of lem-sf-kflat-bifunctor-kinjective-currying curry j into the fixed product
Hom complex. Its signed uncurry is j itself. The chosen nativeOpenTensorModel has this
evaluation normalization by lem-sf-native-normalized-tensor-models.
3. Let O be ordinaryTensorTotal(uT,uP). The normalized models in d identify their model
followed by Q(kappa) with the canonical lax localization tensorator. Totalizing the
underlying balanced tensor identifications gives c with the first conjunct. The map
v = c followed by kappa inverse has coefficient (-1)^(pq) on the reversed summand.
The signed exchange and kappa each contribute this sign, so their composite c has
coefficient 1. Naturality of the sheaf maps preserves both signed differentials.
The underived adjunction agrees under forgetting by lem-sf-native-weil-underived-tensor.
4. Apply lem-sf-native-hom-evaluation-square-all-sources to the Hom comparison of the
fixed nativeDerivedClosedComparison, which is Compatible by native_closed_forgetful.
Its product projections identify forgotten currying with ordinary currying, and its
representative square identifies the corresponding localized Hom arrows. The exact
factors of situation-conventions supply their naturality.
5. Unsigned NativeAdjunctionNormalization in d.models supplies the ordinary uncurry
psi on O. On each left-first (p,q) summand, both u(j) and v followed by psi have the
same sign (-1)^(pq). The Hom projections and the underlying counits agree, so the
coproduct universal property gives u(j) = v followed by psi, also on unbounded totals.
6. Expand derived uncurrying as tensoring with the identity followed by evaluation.
Naturality and evaluation compatibility of the fixed tensorComparison, followed by
counit preservation of d.tensorIso, identify its forgotten native uncurry with the
ordinary one. Substitute steps 2 and 5 and the naturality of the exact factors.
7. Exact forgetting carries j to a quasi-isomorphism. Since v is an isomorphism,
Q(psi) is invertible. Cancel Q(psi), then postcompose with Q(kappa). The two identities
in step 3 give exactly the second conjunct. Zero complexes and the empty scheme use
the same coproduct and localization arguments. -/
theorem native_forget_normalized_binary_models
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeIsKFlat k₀ l X P) (hT : NativeIsKFlat k₀ l X T)
    (d : NativeOrdinaryTensorIdentification k₀ l X) :
    ∃ c : ((Endofunctor.IsoAlgebra.forget
        (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj
          (((nativeTensorTotal k₀ l X).obj P).obj T) ≅
      ((Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P ⊗
      ((Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj T,
      (∀ (p q n : ℤ) (hpq : p + q = n),
        Mod.tensorπ (P.X p).carrier (T.X q).carrier ≫
            ((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
              (nativeOpenTensorInsertion k₀ l X P T p q n hpq)).hom ≫
            (c.hom.f n).hom =
          Mod.tensorObjπ (P.X p).carrier (T.X q).carrier ≫
            (HomologicalComplex.ιTensorObj
              (((Endofunctor.IsoAlgebra.forget
                  (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
              (((Endofunctor.IsoAlgebra.forget
                  (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj T)
              p q n hpq).hom) ∧
      (nativeForget k₀ l X).map (nativeOpenTensorModel k₀ l X P T hP hT).hom ≫
          (Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app
              (((nativeTensorTotal k₀ l X).obj P).obj T) ≫
          DerivedCategory.Q.map c.hom =
        (nativeDerivedClosedComparison k₀ l X).tensorComparison.hom.app
            (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≫
          (d.tensorIso k₀ l).hom.app
            ((nativeForget k₀ l X).obj (DerivedCategory.Q.obj P),
              (nativeForget k₀ l X).obj (DerivedCategory.Q.obj T)) ≫
          (MonoidalCategory.tensor _).map
            (Prod.mkHom
              ((Endofunctor.IsoAlgebra.forget
                  (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app P)
              ((Endofunctor.IsoAlgebra.forget
                  (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app T)) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q
            (((Endofunctor.IsoAlgebra.forget
                (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
            (((Endofunctor.IsoAlgebra.forget
                (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj T)   := by
  classical
  let : (nativeTensorBifunctor k₀ l X).Additive := by
    constructor
    intro A B f g
    apply NatTrans.ext
    funext Q
    exact ((nativeTensorBifunctor k₀ l X).flip.obj Q).map_add
  let : ∀ P : ProEtaleWeilSheaf k₀ l X,
      ((nativeTensorBifunctor k₀ l X).obj P).Additive := by
    intro P
    exact (tensorIhomAdjunction k₀ l X P).left_adjoint_additive
  have hchains := native_weil_tensor_chain k₀ l X
    (nativeTensorBifunctor k₀ l X) (tensorBifunctorForget k₀ l X)
  let chain := hchains.choose
  have hchain := hchains.choose_spec
  rcases d with ⟨⟨m, adjO, evO⟩, βO, hm, hmodels⟩
  dsimp only [WeilConjectures.CoefficientClosedStructure.monoidal] at hm
  subst m
  let S : WeilConjectures.CoefficientClosedStructure
      (nativeDerivedClosedComparison k₀ l X).homModels.ordinaryHom :=
    ⟨inferInstance, adjO, evO⟩
  let model := hmodels.choose
  have hnorm := hmodels.choose_spec.choose_spec.1
  let κ := hmodels.choose_spec.choose_spec.2.2.2.choose
  have hκ := hmodels.choose_spec.choose_spec.2.2.2.choose_spec.1
  have hmodel := hmodels.choose_spec.choose_spec.2.2.2.choose_spec.2
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  let V := U.mapHomologicalComplex (.up ℤ)
  let flip : V.obj (((nativeTensorTotal k₀ l X).obj P).obj T) ≅
      V.obj (CochainComplex.mapBifunctor T P (nativeTensorBifunctor k₀ l X)) :=
    V.mapIso (HomologicalComplex.mapBifunctorFlipIso T P
      (nativeTensorBifunctor k₀ l X) (.up ℤ))
  let c : V.obj (((nativeTensorTotal k₀ l X).obj P).obj T) ≅ V.obj P ⊗ V.obj T :=
    (flip ≪≫ chain T P) ≪≫ κ (V.obj T) (V.obj P)
  refine ⟨c, ?_, ?_⟩
  · intro p q n hpq
    have hqp : q + p = n := by omega
    have hv : U.map (nativeOpenTensorInsertion k₀ l X P T p q n hpq) ≫
          (flip ≪≫ chain T P).hom.f n =
        (q * p).negOnePow • HomologicalComplex.ιMapBifunctor (V.obj T) (V.obj P)
          (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (.up ℤ) q p n hqp := by
      apply forgotten_flip_summand U (nativeTensorBifunctor k₀ l X)
        P T (chain T P).hom p q n hpq
      exact (hchain T P q p n hqp).trans (Category.id_comp _)
    have hc := signed_summand_comp
      (Mod.tensorπ (P.X p).carrier (T.X q).carrier)
      (U.map (nativeOpenTensorInsertion k₀ l X P T p q n hpq)).hom
      ((flip ≪≫ chain T P).hom.f n).hom ((κ (V.obj T) (V.obj P)).hom.f n).hom
      (HomologicalComplex.ιMapBifunctor (V.obj T) (V.obj P)
        (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        (.up ℤ) q p n hqp).hom
      (Mod.tensorObjπ (P.X p).carrier (T.X q).carrier ≫
        (HomologicalComplex.ιTensorObj (V.obj P) (V.obj T) p q n hpq).hom)
      (q * p).negOnePow (Int.units_mul_self _)
      (by simpa only [Mod.comp_hom', Units.smul_def, Mod.zsmul_hom] using
        congrArg (fun z ↦ z.hom) hv)
      (hκ (V.obj T) (V.obj P) q p n hqp hpq)
    simpa only [c, Iso.trans_hom, HomologicalComplex.comp_f, Mod.comp_hom',
      Category.assoc] using hc
  · let C := nativeDerivedClosedComparison k₀ l X
    let M := C.homModels
    let F := nativeForget k₀ l X
    let δ := U.mapDerivedCategoryFactors
    have hC : C.Compatible := by
      unfold C nativeDerivedClosedComparison
      exact (native_closed_forgetful k₀ l X).2.2.2.2.choose_spec
    let N := ((nativeTensorTotal k₀ l X).obj P).obj T
    have hres := Abelian.HasKInjectiveResolutions.exists_isKInjective N
    let I := hres.choose
    have hI := hres.choose_spec.1
    let j := hres.choose_spec.2.choose
    have hj := hres.choose_spec.2.choose_spec.2
    have hnormalized := native_normalized_uncurry_map k₀ l X P T I hP hT hI j
    let φ := hnormalized.choose
    have hψ := hnormalized.choose_spec.1
    have hloc := hnormalized.choose_spec.2
    have hsources := native_hom_evaluation_square_all_sources k₀ l X
      M C.homComparison hC.2.1 T I hI
    have hUI := hsources.choose
    let χ := hsources.choose_spec.choose
    have hχ := hsources.choose_spec.choose_spec.1
    have hs := hsources.choose_spec.choose_spec.2
    let φ' := V.map φ ≫ χ.hom
    have hUP := native_two_sided_kflat_forget k₀ l X P hP
    have hUT := native_two_sided_kflat_forget k₀ l X T hT
    have hnormalized' := hnorm (V.obj T) (V.obj P) (V.obj I) hUT hUP hUI φ'
    let ψ' := hnormalized'.choose
    have hψ' := hnormalized'.choose_spec.1
    have hloc' := hnormalized'.choose_spec.2
    let v := flip ≪≫ chain T P
    have hchain' : V.map j = v.hom ≫ ψ' := by
      apply HomologicalComplex.hom_ext
      intro n
      apply HomologicalComplex.mapBifunctor.hom_ext_of_map U
      intro p q hpq
      change p + q = n at hpq
      have hqp : q + p = n := by omega
      change U.map (HomologicalComplex.ιMapBifunctor P T
          (nativeTensorBifunctor k₀ l X).flip (.up ℤ) p q n hpq) ≫
          U.map (j.f n) = _
      have hi : U.map (HomologicalComplex.ιMapBifunctor P T
            (nativeTensorBifunctor k₀ l X).flip (.up ℤ) p q n hpq) ≫ v.hom.f n =
          (q * p).negOnePow • HomologicalComplex.ιMapBifunctor (V.obj T) (V.obj P)
            (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
            (.up ℤ) q p n hqp := by
        apply forgotten_flip_summand U (nativeTensorBifunctor k₀ l X)
          P T (chain T P).hom p q n hpq
        exact (hchain T P q p n hqp).trans (Category.id_comp _)
      simp only [HomologicalComplex.comp_f]
      refine signed_uncurry_summand U _ _ _ _ _ _ _ (q * p).negOnePow hi
        (by simpa only [mul_comm p q] using hψ p q n hpq) (hψ' q p n hqp) ?_
      have hproj := (Category.assoc (U.map (φ.f p)) (χ.hom.f p)
        (CochainComplex.bifunctorHomπ
          (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (V.obj T) (V.obj I) p q n hqp)).trans
        ((congrArg (U.map (φ.f p) ≫ ·) (hχ p q n hqp)).trans (U.map_comp _ _).symm)
      exact (congrArg (fun z ↦
        ((ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).obj
          ((V.obj T).X q)).map z ≫
            (Mod.ihomAdjunction ((V.obj T).X q)).counit.app ((V.obj I).X n)) hproj).symm
    let f := DerivedCategory.Q.map φ ≫ (M.weilRepresentatives.model T I hI).inv
    let f' := DerivedCategory.Q.map φ' ≫
      (M.ordinaryRepresentatives.model (V.obj T) (V.obj I) hUI).inv
    have hf : F.map f ≫ C.homComparison.hom.app
          (op (DerivedCategory.Q.obj T), DerivedCategory.Q.obj I) =
        δ.hom.app P ≫ f' ≫ M.ordinaryHom.map
          (Prod.mkHom (δ.hom.app T).op (δ.inv.app I)) := by
      simpa only [Functor.comp_map, Functor.map_comp, Category.assoc, f, f', φ'] using
        representative_hom_square DerivedCategory.Q (V ⋙ DerivedCategory.Q) F δ
          M.ordinaryHom P T I _ (M.weilRepresentatives.model T I hI)
          (M.ordinaryRepresentatives.model (V.obj T) (V.obj I) hUI)
          (DerivedCategory.Q.map χ.hom)
          (C.homComparison.hom.app (op (DerivedCategory.Q.obj T), DerivedCategory.Q.obj I))
          hs φ
    have hunc := uncurry_comparison C.weilClosed C.ordinaryClosed F C.tensorComparison
      C.homComparison hC.1 (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj T)
      (DerivedCategory.Q.obj I) f
    simp only [Iso.app_hom, Iso.app_inv] at hunc
    have hunc' := (congrArg
      (C.ordinaryClosed.transpose (F.obj (DerivedCategory.Q.obj P))
        (F.obj (DerivedCategory.Q.obj T)) (F.obj (DerivedCategory.Q.obj I))).symm hf).symm.trans
      hunc
    let ρ := nativeOrdinaryClosedTensorIso C.ordinaryClosed S
    have hmodel' : (model (V.obj T) (V.obj P) hUT).hom ≫
        DerivedCategory.Q.map (κ (V.obj T) (V.obj P)).hom =
        Functor.LaxMonoidal.μ DerivedCategory.Q (V.obj P) (V.obj T) := by
      rw [eq_of_heq (hmodel (V.obj T) (V.obj P) hUT hUP)]
      rw [Category.assoc, ← DerivedCategory.Q.map_comp, Iso.inv_hom_id]
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
    have hψiso : IsIso (DerivedCategory.Q.map ψ') := by
      have : QuasiIso j := hj
      have : IsIso (DerivedCategory.Q.map (V.map j)) := by infer_instance
      rw [hchain', Functor.map_comp] at this
      exact (isIso_comp_left_iff (DerivedCategory.Q.map v.hom)
        (DerivedCategory.Q.map ψ')).mp this
    have hmain : F.map (nativeOpenTensorModel k₀ l X P T hP hT).hom ≫
        δ.hom.app N ≫ DerivedCategory.Q.map v.hom =
      C.tensorComparison.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≫
        ρ.hom.app (F.obj (DerivedCategory.Q.obj P), F.obj (DerivedCategory.Q.obj T)) ≫
        S.tensor.map (Prod.mkHom (δ.hom.app P) (δ.hom.app T)) ≫
        (model (V.obj T) (V.obj P) hUT).hom := by
      exact normalized_model_forget C.ordinaryClosed S
        DerivedCategory.Q (V ⋙ DerivedCategory.Q) F δ P T I N
        (C.tensorComparison.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T))
        (nativeOpenTensorModel k₀ l X P T hP hT).hom j _
        (DerivedCategory.Q.map v.hom) (DerivedCategory.Q.map ψ')
        (model (V.obj T) (V.obj P) hUT).hom f' hloc hloc'
        (by simpa only [Functor.comp_map, Functor.map_comp] using
          congrArg DerivedCategory.Q.map hchain') hunc'
    have hh := congrArg
      (fun z ↦ z ≫ DerivedCategory.Q.map (κ (V.obj T) (V.obj P)).hom) hmain
    simp only [Category.assoc, hmodel'] at hh
    simpa only [C, F, δ, N, S, ρ, V, U, c, v, Iso.trans_hom, Functor.map_comp,
      WeilConjectures.CoefficientClosedStructure.tensor, Category.assoc,
      CategoryTheory.Functor.comp_obj,
      NativeOrdinaryTensorIdentification.tensorIso, NatTrans.comp_app,
      eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id] using hh

end AlgebraicGeometry.ProEtaleWeilSheaf
