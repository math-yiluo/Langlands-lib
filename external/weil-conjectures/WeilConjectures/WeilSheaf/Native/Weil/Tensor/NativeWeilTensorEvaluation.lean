/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.NativeWeilTensorPresentation.NativeWeilTensorPresentation
import all WeilConjectures.WeilSheaf.Native.NativeHomEvaluationSquareAllSources
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRepresentativeUncurry
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRepresentativeCurrying
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact

/-! # Forgetting the representative-normalized native evaluation

Source: Stacks 08J9 and 0A97; native ringed tensor model, evaluation step.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

namespace TensorEvaluationFormal
universe a b
variable {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
  (S : CoefficientClosedStructure H)

private theorem evaluation_iso_naturality {P Q L M : D} (e : P ≅ L) (g : Q ⟶ M) :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom e.inv.op g)) e.hom) ≫
        S.evaluation L M = S.evaluation P Q ≫ g := by
  have h := uncurry_transport S (𝟙 (H.obj (op P, Q))) e.inv g (𝟙 _)
  simp only [Category.id_comp, uncurry_eq] at h
  have hid : S.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, Q))) (𝟙 P)) =
      𝟙 (S.tensor.obj (H.obj (op P, Q), P)) := S.tensor.map_id _
  rw [hid, Category.id_comp] at h
  calc
    _ = S.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, Q))) e.hom) ≫
        S.tensor.map (Prod.mkHom (H.map (Prod.mkHom e.inv.op g)) (𝟙 L)) ≫
          S.evaluation L M := by
      rw [← S.tensor.map_comp_assoc]
      congr 2
      ext <;> simp
    _ = S.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, Q))) e.hom) ≫
        S.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, Q))) e.inv) ≫
          S.evaluation P Q ≫ g := by rw [h]
    _ = _ := by
      rw [← S.tensor.map_comp_assoc]
      simp

private theorem evaluation_of_uncurry
    {E : Type a} [Category.{b} E] {H' : Eᵒᵖ × E ⥤ E}
    (S' : CoefficientClosedStructure H') (F : D ⥤ E)
    (t : S.tensor ⋙ F ≅ F.prod F ⋙ S'.tensor)
    {A K I : D} (e : A ≅ H.obj (op K, I))
    (χ : F.obj (H.obj (op K, I)) ⟶ H'.obj (op (F.obj K), F.obj I))
    (h : F.map ((S.transpose A K I).symm e.hom) =
      t.hom.app (A, K) ≫ (S'.transpose (F.obj A) (F.obj K) (F.obj I)).symm
        (F.map e.hom ≫ χ)) :
    F.map (S.evaluation K I) = t.hom.app (H.obj (op K, I), K) ≫
      S'.tensor.map (Prod.mkHom χ (𝟙 (F.obj K))) ≫
        S'.evaluation (F.obj K) (F.obj I) := by
  rw [uncurry_eq, uncurry_eq, F.map_comp] at h
  have hn := tensor_naturality S S' F t e.hom K
  have : IsIso (Prod.mkHom e.hom (𝟙 K)) := isIso_pair e.hom (𝟙 K)
  apply (cancel_epi (F.map (S.tensor.map (Prod.mkHom e.hom (𝟙 K))))).mp
  rw [h, ← Category.assoc _ (t.hom.app _), hn]
  simp only [Category.assoc, ← S'.tensor.map_comp_assoc]
  congr 2
  apply congrArg S'.tensor.map
  ext <;> simp

-- Cancel a representative model before specializing the evaluation identity.
private theorem evaluation_of_representative
    {E : Type a} [Category.{b} E] {H' : Eᵒᵖ × E ⥤ E}
    (S' : CoefficientClosedStructure H') (F : D ⥤ E)
    (t : S.tensor ⋙ F ≅ F.prod F ⋙ S'.tensor)
    {A K I J : D} (e : A ≅ H.obj (op K, I)) (m : H.obj (op K, I) ≅ J)
    (φ : A ⟶ J) (hφ : φ = e.hom ≫ m.hom)
    (χ : F.obj (H.obj (op K, I)) ⟶ H'.obj (op (F.obj K), F.obj I))
    (h : F.map ((S.transpose A K I).symm (φ ≫ m.inv)) =
      t.hom.app (A, K) ≫ (S'.transpose (F.obj A) (F.obj K) (F.obj I)).symm
        (F.map (φ ≫ m.inv) ≫ χ)) :
    F.map (S.evaluation K I) = t.hom.app (H.obj (op K, I), K) ≫
      S'.tensor.map (Prod.mkHom χ (𝟙 (F.obj K))) ≫
        S'.evaluation (F.obj K) (F.obj I) := by
  have hf : φ ≫ m.inv = e.hom := by
    rw [hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hf] at h
  exact evaluation_of_uncurry S S' F t e χ h

private theorem evaluation_of_iso
    {E : Type a} [Category.{b} E] {H' : Eᵒᵖ × E ⥤ E}
    (S' : CoefficientClosedStructure H') (F : D ⥤ E)
    (t : S.tensor ⋙ F ≅ F.prod F ⋙ S'.tensor)
    (χ : H ⋙ F ≅ F.op.prod F ⋙ H')
    {P Q L M : D} (e : P ≅ L) (e' : Q ≅ M)
    (h : F.map (S.evaluation P Q) =
      t.hom.app (H.obj (op P, Q), P) ≫
        S'.tensor.map (Prod.mkHom (χ.hom.app (op P, Q)) (𝟙 (F.obj P))) ≫
          S'.evaluation (F.obj P) (F.obj Q)) :
    F.map (S.evaluation L M) =
      t.hom.app (H.obj (op L, M), L) ≫
        S'.tensor.map (Prod.mkHom (χ.hom.app (op L, M)) (𝟙 (F.obj L))) ≫
          S'.evaluation (F.obj L) (F.obj M) := by
  let g := H.map (Prod.mkHom e.inv.op e'.hom)
  have : IsIso (Prod.mkHom e.inv.op e'.hom) :=
    isIso_pair e.inv.op e'.hom
  have : IsIso g := inferInstanceAs (IsIso (H.map (Prod.mkHom e.inv.op e'.hom)))
  have : IsIso (Prod.mkHom g e.hom) :=
    isIso_pair g e.hom
  have ht := evaluation_iso_naturality S e e'.hom
  have hu := evaluation_iso_naturality S' (F.mapIso e) (F.map e'.hom)
  have hn := t.hom.naturality (Prod.mkHom g e.hom)
  have hc := χ.hom.naturality (Prod.mkHom e.inv.op e'.hom)
  change F.map g ≫ χ.hom.app _ =
    χ.hom.app _ ≫ H'.map (Prod.mkHom (F.map e.inv).op (F.map e'.hom)) at hc
  change F.map (S.tensor.map (Prod.mkHom g e.hom)) ≫ t.hom.app _ =
    t.hom.app _ ≫ S'.tensor.map (Prod.mkHom (F.map g) (F.map e.hom)) at hn
  apply (cancel_epi (F.map (S.tensor.map (Prod.mkHom g e.hom)))).mp
  calc
    _ = F.map (S.evaluation P Q) ≫ F.map e'.hom := by
      rw [← F.map_comp, ht]
      exact F.map_comp _ _
    _ = t.hom.app (H.obj (op P, Q), P) ≫
        S'.tensor.map (Prod.mkHom (χ.hom.app (op P, Q)) (𝟙 (F.obj P))) ≫
          S'.evaluation (F.obj P) (F.obj Q) ≫ F.map e'.hom := by
      rw [h]
      simp only [Category.assoc]
    _ = t.hom.app (H.obj (op P, Q), P) ≫
        S'.tensor.map (Prod.mkHom (χ.hom.app (op P, Q)) (𝟙 (F.obj P))) ≫
          S'.tensor.map (Prod.mkHom
            (H'.map (Prod.mkHom (F.map e.inv).op (F.map e'.hom))) (F.map e.hom)) ≫
              S'.evaluation (F.obj L) (F.obj M) := by
      simp only [Functor.mapIso_hom, Functor.mapIso_inv] at hu
      rw [hu]
    _ = _ := by
      rw [← Category.assoc (F.map (S.tensor.map _)), hn]
      simp only [Category.assoc, ← S'.tensor.map_comp_assoc]
      congr 2
      apply congrArg S'.tensor.map
      ext
      · exact hc.symm
      · simp

end TensorEvaluationFormal

namespace TensorEvaluation
variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

-- The K-flat replacement and K-injective fullness use the two derived model instances.
private theorem representative_evaluation
    (M : NativeClosedHomModels k₀ l X)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (W : CoefficientClosedStructure M.weilHom)
    (t : W.tensor ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor)
    (N : NativeWeilTensorPresentation k₀ l X M S W.monoidal t)
    (hW : NativeAdjunctionNormalization (HW) N.tensor
      (fun P ↦ N.adjunction.adj P) M.weilHom M.weilRepresentatives W
      (NativeTensorKFlat k₀ l X N.tensor) N.model)
    (χ : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom)
    (hχ : NativeHomRepresentativeCompatibility (HW) (HO)
      M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives (U) χ)
    (P I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeTensorKFlat k₀ l X N.tensor P) (hI : I.IsKInjective) :
    (nativeForget k₀ l X).map
        (W.evaluation (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)) =
      t.hom.app (M.weilHom.obj (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I),
          DerivedCategory.Q.obj P) ≫
        S.tensor.map
          (Prod.mkHom (χ.hom.app (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I))
            (𝟙 ((nativeForget k₀ l X).obj (DerivedCategory.Q.obj P)))) ≫
          S.evaluation ((nativeForget k₀ l X).obj (DerivedCategory.Q.obj P))
            ((nativeForget k₀ l X).obj (DerivedCategory.Q.obj I)) := by
  let F := nativeForget k₀ l X
  let flat := NativeTensorKFlat k₀ l X N.tensor
  let R := ObjectProperty.ι flat ⋙ DerivedCategory.Q
  let V := (HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)).inverseImage
    (ObjectProperty.ι flat)
  let : R.IsLocalization V := N.localization
  let : R.EssSurj := Localization.essSurj R V
  let B := M.weilHom.obj (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I)
  let Q := (R.objPreimage B).obj
  have hQ : flat Q := (R.objPreimage B).property
  let e : DerivedCategory.Q.obj Q ≅ B := R.objObjPreimageIso B
  let := hI
  let := NativeCurrying.hom_isKInjective N.adjunction P I hP
  obtain ⟨φ, hφ⟩ := CochainComplex.IsKInjective.exists_Q_map_eq Q
    (CochainComplex.bifunctorHomObj (HW) P I)
    (e.hom ≫ (M.weilRepresentatives.model P I hI).hom)
  exact TensorEvaluationFormal.evaluation_of_representative W S F t e
    (M.weilRepresentatives.model P I hI) (DerivedCategory.Q.map φ) hφ
    (χ.hom.app (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I))
    (native_weil_representative_uncurry M S W t N hW χ hχ P Q I hP hQ hI φ)

end TensorEvaluation

/-- Forgetting preserves evaluation for closed structures normalized on the
specified tensor and Hom representatives. This is one square on already
specified structures; no structure or comparison is constructed here.

Source: Stacks 08J9 and 0A97; native ringed tensor model, step 3, and the
representative evaluation argument of ringed_forget_normalized_uncurry.
(blueprint: lem-sf-native-weil-tensor-evaluation).

Proof: represent the tensor parameter by a K-flat complex and the target by a
K-injective complex. Resolve the source of evaluation by a K-flat complex.
The native adjunction normalization hW computes its inverse transpose on
these representatives by componentwise uncurrying. The ordinary normalization
N.ordinaryNormalization gives the same formula after forgetting. On each
(p,q) tensor summand, N.underived_uncurry identifies those two arrows, and
N.chain_summand identifies the comparison on total tensors. The product-Hom
projection square hχ identifies the curried arrow. Its restriction to
K-injective source complexes extends to the K-flat source used here by
naturality of the two Hom representative systems and source replacement;
Hom into the K-injective target sends that replacement to an isomorphism
after localization. The model square N.model_forget now gives equality of
the two localized evaluations on the chosen representatives. Cancel their
invertible model and resolution maps. Naturality and the K-flat and
K-injective localization equivalences extend this equality to every K,L.
Finally inverse transposition of the identity is the counit, which is exactly
W.evaluation; this gives the stated square. No associator, unitor, symmetry
or unit-object comparison is used. -/
theorem native_weil_tensor_evaluation
    (M : NativeClosedHomModels k₀ l X)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (W : CoefficientClosedStructure M.weilHom)
    (t : W.tensor ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor)
    (N : NativeWeilTensorPresentation k₀ l X M S W.monoidal t)
    (hW : NativeAdjunctionNormalization (ihomBifunctor k₀ l X) N.tensor
      (fun P ↦ N.adjunction.adj P) M.weilHom M.weilRepresentatives W
      (NativeTensorKFlat k₀ l X N.tensor) N.model)
    (χ : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom)
    (hχ : NativeHomRepresentativeCompatibility (ihomBifunctor k₀ l X)
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) χ) :
    ∀ K L, (nativeForget k₀ l X).map (W.evaluation K L) =
      t.hom.app (M.weilHom.obj (op K, L), K) ≫
        S.tensor.map
          (X := ((nativeForget k₀ l X).obj (M.weilHom.obj (op K, L)),
            (nativeForget k₀ l X).obj K))
          (Y := (M.ordinaryHom.obj
            (op ((nativeForget k₀ l X).obj K), (nativeForget k₀ l X).obj L),
            (nativeForget k₀ l X).obj K))
          (Prod.mkHom (χ.hom.app (op K, L)) (𝟙 ((nativeForget k₀ l X).obj K))) ≫
          S.evaluation ((nativeForget k₀ l X).obj K) ((nativeForget k₀ l X).obj L) := by
  intro K L
  let flat := NativeTensorKFlat k₀ l X N.tensor
  let R := ObjectProperty.ι flat ⋙ DerivedCategory.Q
  let V := (HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)).inverseImage
    (ObjectProperty.ι flat)
  let : R.IsLocalization V := N.localization
  let : R.EssSurj := Localization.essSurj R V
  let P := (R.objPreimage K).obj
  have hP : flat P := (R.objPreimage K).property
  let e : DerivedCategory.Q.obj P ≅ K := R.objObjPreimageIso K
  let I := DerivedCategory.kInjectiveRep L
  let e' := (DerivedCategory.kInjectiveRepIso L).symm
  exact TensorEvaluationFormal.evaluation_of_iso W S (nativeForget k₀ l X) t χ e e'
    (TensorEvaluation.representative_evaluation M S W t N hW χ hχ P I hP inferInstance)

end AlgebraicGeometry.ProEtaleWeilSheaf
