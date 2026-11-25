/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.NativeWeilTensorPresentation.NativeWeilTensorPresentation
import all WeilConjectures.WeilSheaf.Native.NativeHomEvaluationSquareAllSources
import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilChainUncurryForget

/-! # Forgetting uncurrying on native tensor representatives -/

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

private theorem remove_model {E : Type a} [Category.{b} E] (F : D ⥤ E)
    {A B T : D} {A' B' : E} (e : A ≅ B) (e' : A' ≅ B')
    (x : F.obj A ⟶ A') (y : F.obj B ⟶ B')
    (h : x ≫ e'.hom = F.map e.hom ≫ y) (f : T ⟶ B) :
    F.map (f ≫ e.inv) ≫ x = F.map f ≫ y ≫ e'.inv := by
  apply (cancel_mono e'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, ← F.map_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem remove_model_natural
    {C E : Type a} [Category.{b} C] [Category.{b} E]
    (Q : C ⥤ D) (V : C ⥤ E) (F : D ⥤ E) (δ : Q ⋙ F ≅ V)
    {T J : C} {A : D} {B B' : E} (e : A ≅ Q.obj J) (e' : B ≅ B')
    (c : V.obj J ⟶ B') (x : F.obj A ⟶ B)
    (h : x ≫ e'.hom = F.map e.hom ≫ δ.hom.app J ≫ c) (f : T ⟶ J) :
    F.map (Q.map f ≫ e.inv) ≫ x =
      δ.hom.app T ≫ V.map f ≫ c ≫ e'.inv := by
  have hm := remove_model F e e' x (δ.hom.app J ≫ c) h (Q.map f)
  rw [hm]
  have hn : F.map (Q.map f) ≫ δ.hom.app J = δ.hom.app T ≫ V.map f :=
    δ.hom.naturality f
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ c ≫ e'.inv) hn

private theorem invert_hom_square (G : Dᵒᵖ × D ⥤ D)
    {A B P Q T : D} (e : A ≅ B) (e' : P ≅ Q)
    (x : T ⟶ G.obj (op A, P)) (y : T ⟶ G.obj (op B, Q))
    (h : x ≫ G.map (Prod.mkHom e.inv.op e'.hom) = y) :
    x = y ≫ G.map (Prod.mkHom e.hom.op e'.inv) := by
  rw [← h, Category.assoc, ← G.map_comp]
  simp

private theorem tensor_naturality {E : Type a} [Category.{b} E]
    {H' : Eᵒᵖ × E ⥤ E} (S' : CoefficientClosedStructure H') (F : D ⥤ E)
    (t : S.tensor ⋙ F ≅ F.prod F ⋙ S'.tensor)
    {A B : D} (f : A ⟶ B) (K : D) :
    F.map (S.tensor.map (Prod.mkHom f (𝟙 K))) ≫ t.hom.app (B, K) =
      t.hom.app (A, K) ≫ S'.tensor.map (Prod.mkHom (F.map f) (𝟙 (F.obj K))) := by
  simpa using t.hom.naturality (Prod.mkHom f (𝟙 K))

private theorem uncurry_eq (A K L : D) (f : A ⟶ H.obj (op K, L)) :
    (S.transpose A K L).symm f =
      S.tensor.map (Prod.mkHom f (𝟙 K)) ≫ S.evaluation K L := by
  let := S.monoidal
  simp [CoefficientClosedStructure.transpose, CoefficientClosedStructure.evaluation,
    CoefficientClosedStructure.tensor, Adjunction.homEquiv, MonoidalCategory.tensor]

private theorem uncurry_source {A A' K L : D} (a : A' ⟶ A)
    (f : A ⟶ H.obj (op K, L)) :
    (S.transpose A' K L).symm (a ≫ f) =
      S.tensor.map (Prod.mkHom a (𝟙 K)) ≫ (S.transpose A K L).symm f := by
  rw [uncurry_eq, uncurry_eq, ← S.tensor.map_comp_assoc]
  congr 2
  exact Prod.ext rfl (Category.id_comp _).symm

private theorem uncurry_parameter {A K K' L : D} (a : K' ⟶ K)
    (f : A ⟶ H.obj (op K, L)) :
    (S.transpose A K' L).symm (f ≫ H.map (Prod.mkHom a.op (𝟙 L))) =
      S.tensor.map (Prod.mkHom (𝟙 A) a) ≫ (S.transpose A K L).symm f := by
  have he : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom a.op (𝟙 L))) (𝟙 K')) ≫
      S.evaluation K' L =
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, L))) a) ≫ S.evaluation K L := by
    let := S.monoidal
    simpa only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
      MonoidalCategory.tensor_map, MonoidalCategory.tensorRight,
      MonoidalCategory.tensorLeft, Functor.flip, MonoidalCategory.curriedTensor,
      MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
      S.evaluation_naturality K K' L a
  rw [uncurry_eq, uncurry_eq]
  calc
    _ = S.tensor.map (Prod.mkHom f (𝟙 K')) ≫
        S.tensor.map (Prod.mkHom (H.map (Prod.mkHom a.op (𝟙 L))) (𝟙 K')) ≫
          S.evaluation K' L := by
      rw [← S.tensor.map_comp_assoc]
      congr 2
      exact Prod.ext rfl (Category.id_comp _).symm
    _ = S.tensor.map (Prod.mkHom f (𝟙 K')) ≫
        S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, L))) a) ≫ S.evaluation K L := by rw [he]
    _ = _ := by
      simp only [← S.tensor.map_comp_assoc]
      congr 2
      ext <;> simp

private theorem uncurry_target {A K L L' : D} (a : L ⟶ L')
    (f : A ⟶ H.obj (op K, L)) :
    (S.transpose A K L').symm (f ≫ H.map (Prod.mkHom (𝟙 (op K)) a)) =
      (S.transpose A K L).symm f ≫ a :=
  (S.adjunction K).homEquiv_naturality_right_symm f a

private theorem uncurry_transport {A A' K K' L L' : D}
    (a : A' ⟶ A) (b : K' ⟶ K) (c : L ⟶ L')
    (f : A ⟶ H.obj (op K, L)) :
    (S.transpose A' K' L').symm (a ≫ f ≫ H.map (Prod.mkHom b.op c)) =
      S.tensor.map (Prod.mkHom a b) ≫ (S.transpose A K L).symm f ≫ c := by
  have hh : H.map (Prod.mkHom b.op c) =
      H.map (Prod.mkHom b.op (𝟙 L)) ≫ H.map (Prod.mkHom (𝟙 (op K')) c) := by
    rw [← H.map_comp]
    congr 1
    ext <;> simp
  rw [hh]
  rw [uncurry_source, ← Category.assoc f, uncurry_target, uncurry_parameter]
  simp only [Category.assoc, ← S.tensor.map_comp_assoc]
  congr 2
  ext <;> simp

private theorem localized_uncurry
    {C E : Type a} [Category.{b} C] [Category.{b} E]
    {H' : Eᵒᵖ × E ⥤ E} (S' : CoefficientClosedStructure H')
    (Q : C ⥤ D) (V : C ⥤ E) (F : D ⥤ E) (δ : Q ⋙ F ≅ V)
    (t : S.tensor ⋙ F ≅ F.prod F ⋙ S'.tensor)
    (P R I T : C) (B : E)
    (e : S.tensor.obj (Q.obj R, Q.obj P) ≅ Q.obj T)
    (e' : S'.tensor.obj (V.obj R, V.obj P) ≅ B) (c : V.obj T ≅ B)
    (ψ : T ⟶ I) (ψ' : B ⟶ V.obj I)
    (f : Q.obj R ⟶ H.obj (op (Q.obj P), Q.obj I))
    (f' : V.obj R ⟶ H'.obj (op (V.obj P), V.obj I))
    (g : F.obj (Q.obj R) ⟶ H'.obj (op (F.obj (Q.obj P)), F.obj (Q.obj I)))
    (hf : g = δ.hom.app R ≫ f' ≫
      H'.map (Prod.mkHom (δ.hom.app P).op (δ.inv.app I)))
    (hloc : e.hom ≫ Q.map ψ = (S.transpose _ _ _).symm f)
    (hloc' : e'.hom ≫ ψ' = (S'.transpose _ _ _).symm f')
    (hc : V.map ψ = c.hom ≫ ψ')
    (ht : F.map e.hom ≫ δ.hom.app T ≫ c.hom = t.hom.app (Q.obj R, Q.obj P) ≫
      S'.tensor.map (Prod.mkHom (δ.hom.app R) (δ.hom.app P)) ≫ e'.hom) :
    F.map ((S.transpose _ _ _).symm f) =
      t.hom.app (Q.obj R, Q.obj P) ≫ (S'.transpose _ _ _).symm g := by
  have hu := uncurry_transport S' (δ.hom.app R) (δ.hom.app P) (δ.inv.app I) f'
  rw [← hf] at hu
  rw [← hloc, F.map_comp]
  have hn : F.map (Q.map ψ) ≫ δ.hom.app I = δ.hom.app T ≫ V.map ψ :=
    δ.hom.naturality ψ
  have hn' : F.map (Q.map ψ) = δ.hom.app T ≫ V.map ψ ≫ δ.inv.app I := by
    apply (cancel_mono (δ.hom.app I)).mp
    simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using hn
  calc
    _ = F.map e.hom ≫ δ.hom.app T ≫ c.hom ≫ ψ' ≫ δ.inv.app I := by
      rw [hn', hc]
      simp only [Category.assoc]
    _ = t.hom.app (Q.obj R, Q.obj P) ≫
        S'.tensor.map (Prod.mkHom (δ.hom.app R) (δ.hom.app P)) ≫
          e'.hom ≫ ψ' ≫ δ.inv.app I := by rw [reassoc_of% ht]
    _ = _ := by
      rw [← Category.assoc e'.hom, hloc', ← hu]
      rfl

-- Assemble the model and localization squares in arbitrary categories, so their
-- rewrites do not unfold the concrete derived-category instances.
private theorem localized_uncurry_of_representatives
    {C C' E : Type a} [Category.{b} C] [Category.{b} C'] [Category.{b} E]
    {H' : Eᵒᵖ × E ⥤ E} (S' : CoefficientClosedStructure H')
    (Q : C ⥤ D) (Q' : C' ⥤ E) (U : C ⥤ C') (F : D ⥤ E)
    (δ : Q ⋙ F ≅ U ⋙ Q') (t : S.tensor ⋙ F ≅ F.prod F ⋙ S'.tensor)
    (P R I T J : C) (B J' : C')
    (e : S.tensor.obj (Q.obj R, Q.obj P) ≅ Q.obj T)
    (e' : S'.tensor.obj (Q'.obj (U.obj R), Q'.obj (U.obj P)) ≅ Q'.obj B)
    (c : U.obj T ≅ B) (m : H.obj (op (Q.obj P), Q.obj I) ≅ Q.obj J)
    (m' : H'.obj (op (Q'.obj (U.obj P)), Q'.obj (U.obj I)) ≅ Q'.obj J')
    (d : U.obj J ≅ J')
    (x : F.obj (H.obj (op (Q.obj P), Q.obj I)) ⟶
      H'.obj (op (F.obj (Q.obj P)), F.obj (Q.obj I)))
    (hs : x ≫ H'.map (Prod.mkHom (δ.inv.app P).op (δ.hom.app I)) ≫ m'.hom =
      F.map m.hom ≫ δ.hom.app J ≫ Q'.map d.hom)
    (φ : R ⟶ J) (ψ : T ⟶ I) (ψ' : B ⟶ U.obj I)
    (hloc : e.hom ≫ Q.map ψ = (S.transpose _ _ _).symm (Q.map φ ≫ m.inv))
    (hloc' : e'.hom ≫ Q'.map ψ' =
      (S'.transpose _ _ _).symm (Q'.map (U.map φ ≫ d.hom) ≫ m'.inv))
    (hc : c.inv ≫ U.map ψ = ψ')
    (ht : F.map e.hom ≫ δ.hom.app T ≫ Q'.map c.hom =
      t.hom.app (Q.obj R, Q.obj P) ≫
        S'.tensor.map (Prod.mkHom (δ.hom.app R) (δ.hom.app P)) ≫ e'.hom) :
    F.map ((S.transpose _ _ _).symm (Q.map φ ≫ m.inv)) =
      t.hom.app (Q.obj R, Q.obj P) ≫
        (S'.transpose _ _ _).symm (F.map (Q.map φ ≫ m.inv) ≫ x) := by
  let f := Q.map φ ≫ m.inv
  let f' := Q'.map (U.map φ ≫ d.hom) ≫ m'.inv
  have hf : F.map f ≫ x ≫
      H'.map (Prod.mkHom (δ.inv.app P).op (δ.hom.app I)) = δ.hom.app R ≫ f' := by
    have hm := remove_model_natural Q (U ⋙ Q') F δ m m' (Q'.map d.hom)
      (x ≫ H'.map (Prod.mkHom (δ.inv.app P).op (δ.hom.app I)))
      (by simpa only [Category.assoc] using hs) φ
    simpa only [Functor.comp_map, Functor.map_comp, Category.assoc, f, f'] using hm
  have hf' : F.map f ≫ x = δ.hom.app R ≫ f' ≫
      H'.map (Prod.mkHom (δ.hom.app P).op (δ.inv.app I)) := by
    have hh := invert_hom_square H' (δ.app P) (δ.app I)
      (F.map f ≫ x) (δ.hom.app R ≫ f')
      (by simpa only [Category.assoc, Iso.app_inv, Iso.app_hom] using hf)
    simpa only [Category.assoc, Iso.app_inv, Iso.app_hom] using hh
  exact localized_uncurry S S' Q (U ⋙ Q') F δ t P R I T (Q'.obj B)
    e e' (Q'.mapIso c) ψ (Q'.map ψ') f f' (F.map f ≫ x) hf' hloc hloc'
    (by simpa only [Functor.comp_map, Functor.map_comp, Functor.mapIso_hom] using
      congrArg Q'.map ((Iso.inv_comp_eq c).mp hc)) ht

end TensorEvaluationFormal

open TensorEvaluation
variable {k₀ l X}

-- The proof combines both normalizations and their dependent representative isomorphisms.
/-- Forgetting commutes with inverse transposition on K-flat tensor representatives
and a K-injective target.

Source: Stacks 08J9 and 0A97; native tensor-model evaluation argument, tensor-summand
and localized-uncurrying steps.
(blueprint: lem-sf-native-weil-representative-uncurry).

Proof: extend the Hom comparison to the K-flat source using source replacement.
Apply the native and ordinary adjunction normalizations to a curried chain map.
On each tensor summand, the specified underived uncurrying square identifies the
two component arrows. The total-tensor comparison and the coproduct universal
property identify the chain maps. Localize this equality and paste the supplied
model-forgetting square and the Hom comparison square. Naturality of inverse
transposition along the factorization isomorphisms gives the displayed identity. -/
theorem native_weil_representative_uncurry
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
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) χ)
    (P Q I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeTensorKFlat k₀ l X N.tensor P)
    (hQ : NativeTensorKFlat k₀ l X N.tensor Q) (hI : I.IsKInjective)
    (φ : Q ⟶ CochainComplex.bifunctorHomObj (ihomBifunctor k₀ l X) P I) :
    let f := DerivedCategory.Q.map φ ≫ (M.weilRepresentatives.model P I hI).inv
    (nativeForget k₀ l X).map
        ((W.transpose (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj I)).symm f) =
      t.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≫
        (S.transpose ((nativeForget k₀ l X).obj (DerivedCategory.Q.obj Q))
          ((nativeForget k₀ l X).obj (DerivedCategory.Q.obj P))
          ((nativeForget k₀ l X).obj (DerivedCategory.Q.obj I))).symm
          ((nativeForget k₀ l X).map f ≫
            χ.hom.app (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I)) := by
  let F := nativeForget k₀ l X
  let δ := (U (k₀ := k₀) (l := l) (X := X)).mapDerivedCategoryFactors
  -- Projections keep the witnesses shared without constructing large elimination motives.
  have hsources := native_hom_evaluation_square_all_sources k₀ l X M χ hχ P I hI
  have hUI := hsources.choose
  let c := hsources.choose_spec.choose
  have hc := hsources.choose_spec.choose_spec.1
  have hs := hsources.choose_spec.choose_spec.2
  let φ' := (UC).map φ ≫ c.hom
  have hnorm := hW P Q I hP hQ hI φ
  let ψ := hnorm.choose
  have hψ := hnorm.choose_spec.1
  have hloc := hnorm.choose_spec.2
  have hnorm' := N.ordinaryNormalization ((UC).obj P) ((UC).obj Q)
    ((UC).obj I) (N.preserves_flat P hP) (N.preserves_flat Q hQ) hUI φ'
  let ψ' := hnorm'.choose
  have hψ' := hnorm'.choose_spec.1
  have hloc' := hnorm'.choose_spec.2
  exact TensorEvaluationFormal.localized_uncurry_of_representatives W S
    DerivedCategory.Q DerivedCategory.Q (UC) F δ t P Q I
    (CochainComplex.mapBifunctor P Q N.tensor)
    (CochainComplex.bifunctorHomObj (HW) P I) _ _
    (N.model P Q hP)
    (N.ordinaryModel ((UC).obj P) ((UC).obj Q) (N.preserves_flat P hP))
    (N.chain P Q) (M.weilRepresentatives.model P I hI)
    (M.ordinaryRepresentatives.model ((UC).obj P) ((UC).obj I) hUI) c
    (χ.hom.app (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I))
    hs φ ψ ψ' hloc hloc'
    (native_weil_chain_uncurry_forget M S W t N P Q I c hc φ ψ ψ' hψ hψ')
    (N.model_forget P Q hP)

end AlgebraicGeometry.ProEtaleWeilSheaf
