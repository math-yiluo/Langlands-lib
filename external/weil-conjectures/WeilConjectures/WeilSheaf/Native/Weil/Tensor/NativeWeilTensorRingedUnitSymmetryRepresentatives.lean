/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModel
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorForgetKFlat
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorDescent
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedLeftUnitRepresentatives
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapLocalization

/-! # Coherence component of the native ringed derived square

Source: Stacks 06YU, 0FPT; blueprint step 3 of
`lem-sf-native-weil-tensor-ringed-derived-square-native-data`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

section BraidedComparison

variable {B D : Type*} [Category B] [Category D]
  [MonoidalCategory B] [MonoidalCategory D] [SymmetricCategory B] [SymmetricCategory D]
  (F : B ⥤ D) (t : MonoidalCategory.tensor B ⋙ F ≅ F.prod F ⋙ MonoidalCategory.tensor D)

/-- Equality of the two normalized model squares implies the braiding square. -/
private theorem braiding_of_models (P Q : B) {Z Z' : D}
    (n : F.obj (P ⊗ Q) ≅ Z) (n' : F.obj (Q ⊗ P) ≅ Z')
    (o : F.obj P ⊗ F.obj Q ≅ Z) (o' : F.obj Q ⊗ F.obj P ≅ Z')
    (s : Z ⟶ Z')
    (hn : n.hom = t.hom.app (P, Q) ≫ o.hom)
    (hn' : n'.hom = t.hom.app (Q, P) ≫ o'.hom)
    (hs : F.map (β_ P Q).hom ≫ n'.hom = n.hom ≫ s)
    (ho : (β_ (F.obj P) (F.obj Q)).hom ≫ o'.hom = o.hom ≫ s) :
    F.map (β_ P Q).hom ≫ t.hom.app (Q, P) =
      t.hom.app (P, Q) ≫ (β_ (F.obj P) (F.obj Q)).hom := by
  apply (cancel_mono o'.hom).mp
  simpa only [hn, hn', Category.assoc, ho] using hs

/-- The braiding equation transfers across isomorphisms in both inputs. -/
private theorem braiding_of_iso {P Q P' Q' : B} (e : P ≅ P') (e' : Q ≅ Q')
    (h : F.map (β_ P Q).hom ≫ t.hom.app (Q, P) =
      t.hom.app (P, Q) ≫ (β_ (F.obj P) (F.obj Q)).hom) :
    F.map (β_ P' Q').hom ≫ t.hom.app (Q', P') =
      t.hom.app (P', Q') ≫ (β_ (F.obj P') (F.obj Q')).hom := by
  apply (cancel_epi (F.map (e.hom ⊗ₘ e'.hom))).mp
  change F.map (e.hom ⊗ₘ e'.hom) ≫ F.map (β_ P' Q').hom ≫ _ =
    F.map (e.hom ⊗ₘ e'.hom) ≫ t.hom.app (P', Q') ≫ (β_ _ _).hom
  rw [← F.map_comp_assoc, BraidedCategory.braiding_naturality, F.map_comp,
    Category.assoc]
  have hn := t.hom.naturality (X := (Q, P)) (Y := (Q', P'))
    (Prod.mkHom e'.hom e.hom)
  have hn' := t.hom.naturality (X := (P, Q)) (Y := (P', Q'))
    (Prod.mkHom e.hom e'.hom)
  simp only [Functor.comp_map, Functor.prod_map, tensor_map] at hn hn'
  erw [hn, reassoc_of% hn', ← Category.assoc, h, Category.assoc,
    BraidedCategory.braiding_naturality]
  rfl

/-- A braiding square for tensor models is preserved by changing both inputs. -/
private theorem braiding_model_of_iso {P Q P' Q' Z Z' : D}
    (a : P ≅ P') (a' : Q ≅ Q') (o : P' ⊗ Q' ≅ Z) (o' : Q' ⊗ P' ≅ Z')
    (s : Z ⟶ Z') (h : (β_ P' Q').hom ≫ o'.hom = o.hom ≫ s) :
    (β_ P Q).hom ≫ ((MonoidalCategory.tensor D).mapIso (a'.prod a) ≪≫ o').hom =
      ((MonoidalCategory.tensor D).mapIso (a.prod a') ≪≫ o).hom ≫ s := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, tensor_map, Category.assoc]
  rw [← BraidedCategory.braiding_naturality_assoc, h]

/-- A left-unit equation and the braiding equation imply the right-unit equation. -/
private theorem right_unit_of_left (ε : F.obj (𝟙_ B) ≅ 𝟙_ D) (P : B)
    (hl : t.hom.app (𝟙_ B, P) ≫ (ε.hom ⊗ₘ 𝟙 _) ≫
      (λ_ (F.obj P)).hom = F.map (λ_ P).hom)
    (hs : F.map (β_ P (𝟙_ B)).hom ≫ t.hom.app (𝟙_ B, P) =
      t.hom.app (P, 𝟙_ B) ≫ (β_ (F.obj P) (F.obj (𝟙_ B))).hom) :
    t.hom.app (P, 𝟙_ B) ≫ (𝟙 _ ⊗ₘ ε.hom) ≫
      (ρ_ (F.obj P)).hom = F.map (ρ_ P).hom := by
  calc
    _ = t.hom.app (P, 𝟙_ B) ≫ (𝟙 _ ⊗ₘ ε.hom) ≫
        (β_ (F.obj P) (𝟙_ D)).hom ≫ (λ_ (F.obj P)).hom := by
      rw [braiding_leftUnitor]
    _ = t.hom.app (P, 𝟙_ B) ≫ (β_ (F.obj P) (F.obj (𝟙_ B))).hom ≫
        (ε.hom ⊗ₘ 𝟙 _) ≫ (λ_ (F.obj P)).hom := by
      simpa only [Category.assoc, Functor.prod_obj] using
        congrArg (fun f ↦ t.hom.app (P, 𝟙_ B) ≫ f ≫ (λ_ (F.obj P)).hom)
          (BraidedCategory.braiding_naturality (𝟙 (F.obj P)) ε.hom)
    _ = F.map (β_ P (𝟙_ B)).hom ≫ t.hom.app (𝟙_ B, P) ≫
        (ε.hom ⊗ₘ 𝟙 _) ≫ (λ_ (F.obj P)).hom := by
      simpa only [Category.assoc, Functor.prod_obj] using
        congrArg (fun f ↦ f ≫ (ε.hom ⊗ₘ 𝟙 (F.obj P)) ≫ (λ_ (F.obj P)).hom) hs.symm
    _ = F.map (β_ P (𝟙_ B)).hom ≫ F.map (λ_ P).hom := by rw [hl]
    _ = F.map (ρ_ P).hom := by
      rw [← F.map_comp, braiding_leftUnitor]

end BraidedComparison

attribute [local irreducible] Functor.mapDerivedCategory
  nativeWeilRingedMonoidal nativeWeilRingedSymmetric nativeWeilRingedTensorModel
  Functor.mapDerivedCategoryFactors DerivedCategory DerivedCategory.Q
  instCategoryDerivedCategory NativeOrdinaryKFlat NativeTensorKFlat

-- The normalization compares independently presented total-complex models.
/-- Unit and signed-symmetry squares on native K-flat representatives.

Source: Stacks 06YU, 0FPT; native tensor transport, unit and symmetry parts of step 3.
(blueprint: lem-sf-native-weil-tensor-ringed-unit-symmetry-representatives).

Proof: obtain one epsilon and the left-unit equation from the left-unit
representative calculation. The signed balanced-summand equations identify the
two canonical total comparisons by tensor and coproduct extensionality; their
heterogeneous normalization equations then identify the ordinary derived tensor
models on two K-flat inputs. For a pair of native K-flat representatives, hforget
identifies the native model comparison with t followed by the ordinary model.
The localized signed-swap calculation supplies the native braiding square;
the braiding square in hS supplies the ordinary one. Cancel the ordinary model
to obtain the symmetry equation for t. Naturality and the essential surjectivity
of K-flat localization from A.localization transfer this equation to any two
derived inputs, in particular to a pair containing the tensor unit. Finally use
rho_P = beta(P,1);lambda_P, naturality of the ordinary braiding with respect to
epsilon, and the left-unit equation to prove the right-unit equation with the
same epsilon. The left-unit and localized signed-swap calculations are separate
named lemmas; all model identification, cancellation and transfer steps are
proved here. Zero complexes, empty sites and all integer degrees are included. -/
theorem native_weil_tensor_ringed_unit_symmetry_representatives
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X)
    [T.Additive] [∀ P, (T.obj P).Additive]
    (adj : T ⊣₂ ihomBifunctor k₀ l X)
    (e : Functor.uncurry.obj T ⋙
        Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ≅
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).prod
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) ⋙
          Functor.uncurry.obj
            (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    (he : ∀ (P Q I : ProEtaleWeilSheaf k₀ l X)
      (f : Q ⟶ ((ihomBifunctor k₀ l X).obj (op P)).obj I),
      e.inv.app (P, Q) ≫
          (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
            (((adj.adj P).homEquiv Q I).symm f) =
        ((Mod.ihomAdjunction P.carrier).homEquiv Q.carrier I.carrier).symm f.hom.f)
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (chain : ∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
      ((Endofunctor.IsoAlgebra.forget
        (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q T) ≅
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q))
    (hchain : ∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (p q n : ℤ) (h : p + q = n),
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
          (HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p q n h) ≫
            (chain P Q).hom.f n =
        e.hom.app (P.X p, Q.X q) ≫ HomologicalComplex.ιMapBifunctor
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q)
          (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (.up ℤ) p q n h)
    (b : NativeWeilTensorRingedBridge k₀ l X)
    [HasDerivedCategory.{u + 2} (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)]
    [HasDerivedCategory.{u + 2} (RingedTensorModules.{u + 1, u + 1, u + 1} b.K b.Q)]
    (A : NativeWeilRingedTensorComplexes b T adj)
    (M : NativeClosedHomModels k₀ l X)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (β : @SymmetricCategory _ _ S.monoidal)
    (hmonoidal : S.monoidal = (inferInstance : MonoidalCategory
      (DerivedCategory (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))))
    (hS : NativeOrdinaryTensorModels l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      M.ordinaryHom M.ordinaryRepresentatives S β)
    (SB : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u + 1, u + 1, u + 2} b.J b.R))
    (TB : CoefficientTensorModels.{u + 1, u + 1, u + 1, u + 2} b.J b.R SB)
    (βB : @SymmetricCategory _ _ SB.monoidal)
    (cB : RingedDerivedTensorCoherence b.J b.R SB TB βB)
    (SA : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u + 1, u + 1, u + 2} b.K b.Q))
    (TA : CoefficientTensorModels.{u + 1, u + 1, u + 1, u + 2} b.K b.Q SA)
    (βA : @SymmetricCategory _ _ SA.monoidal)
    (cA : RingedDerivedTensorCoherence b.K b.Q SA TA βA)
    (d : RingedForgetTensorTransposition.TensorComparison
      b.J b.R b.K b.Q b.forget b.underived SB TB βB cB SA TA βA cA)
    (ordinaryModel : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
        (_ : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P),
          S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
            DerivedCategory.Q.obj
              (ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q))
    (hcanonical : ∃ κ : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ,
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q ≅ Q ⊗ P,
      (∀ (P Q : CochainComplex (ProEtale.AdicSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
        (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n),
        Mod.tensorπ (Q.X q) (P.X p) ≫
            (HomologicalComplex.ιMapBifunctor P Q
              (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
              (.up ℤ) p q n hpq).hom ≫ ((κ P Q).hom.f n).hom =
          (p * q).negOnePow •
            (Mod.tensorObjπ (Q.X q) (P.X p) ≫
              (HomologicalComplex.ιTensorObj Q P q p n hqp).hom)) ∧
      ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
        (hP : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P)
        (_hQ : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber Q),
        HEq (ordinaryModel P Q hP).hom
          (Functor.LaxMonoidal.μ DerivedCategory.Q Q P ≫
            DerivedCategory.Q.map (κ P Q).inv))
    (_hnaturality : ∀ (P Q P' Q' : CochainComplex (ProEtale.AdicSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
          (hP : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P)
          (hP' : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P')
          (f : P ⟶ P') (g : Q ⟶ Q'),
        S.tensor.map
            (X := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
            (Y := (DerivedCategory.Q.obj Q', DerivedCategory.Q.obj P'))
            (Prod.mkHom (DerivedCategory.Q.map g) (DerivedCategory.Q.map f)) ≫
            (ordinaryModel P' Q' hP').hom =
          (ordinaryModel P Q hP).hom ≫ DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap f g
              (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
              (.up ℤ)))
    (t : @MonoidalCategory.tensor _ _ (nativeWeilRingedMonoidal b SB) ⋙
        nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor)
    (hforget : (∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hP : NativeTensorKFlat k₀ l X T P),
    (nativeForget k₀ l X).map (nativeWeilRingedTensorModel b T adj A SB TB βB cB P Q hP).hom ≫
        ((Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app
            (CochainComplex.mapBifunctor P Q T)) ≫
        DerivedCategory.Q.map (chain P Q).hom =
      t.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≫
        S.tensor.map
          (X := ((nativeForget k₀ l X).obj (DerivedCategory.Q.obj Q),
            (nativeForget k₀ l X).obj (DerivedCategory.Q.obj P)))
          (Y := (DerivedCategory.Q.obj
            (((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q),
            DerivedCategory.Q.obj
            (((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)))
          (Prod.mkHom
            ((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app Q)
            ((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app P)) ≫
        (ordinaryModel
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q)
          (native_weil_tensor_forget_kflat k₀ l X T chain P hP)).hom)) :
    let m := nativeWeilRingedMonoidal b SB
    let F := nativeForget k₀ l X
    ∃ ε : F.obj m.tensorUnit ≅ S.monoidal.tensorUnit,
      (∀ (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ),
        NativeTensorKFlat k₀ l X T P →
        (t.hom.app (m.tensorUnit, DerivedCategory.Q.obj P) ≫
            S.tensor.map
              (X := (F.obj m.tensorUnit, F.obj (DerivedCategory.Q.obj P)))
              (Y := (S.monoidal.tensorUnit, F.obj (DerivedCategory.Q.obj P)))
              (ε.hom, 𝟙 _) ≫ (S.monoidal.leftUnitor (F.obj (DerivedCategory.Q.obj P))).hom =
          F.map (m.leftUnitor (DerivedCategory.Q.obj P)).hom) ∧
        (t.hom.app (DerivedCategory.Q.obj P, m.tensorUnit) ≫
            S.tensor.map
              (X := (F.obj (DerivedCategory.Q.obj P), F.obj m.tensorUnit))
              (Y := (F.obj (DerivedCategory.Q.obj P), S.monoidal.tensorUnit))
              (𝟙 _, ε.hom) ≫ (S.monoidal.rightUnitor (F.obj (DerivedCategory.Q.obj P))).hom =
          F.map (m.rightUnitor (DerivedCategory.Q.obj P)).hom)) ∧
      (∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ),
        NativeTensorKFlat k₀ l X T P → NativeTensorKFlat k₀ l X T Q →
        F.map ((nativeWeilRingedSymmetric b SB βB).toBraidedCategory.braiding
            (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
            t.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) =
          t.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
            (β.toBraidedCategory.braiding (F.obj (DerivedCategory.Q.obj P))
              (F.obj (DerivedCategory.Q.obj Q))).hom) := by
  classical
  refine (native_weil_tensor_ringed_left_unit_representatives
    k₀ l X T adj e he chain hchain b A M S hmonoidal
    SB TB βB cB SA TA βA cA d ordinaryModel hcanonical _hnaturality t hforget).elim ?_
  intro ε hl
  clear _hnaturality d cA βA TA SA hmonoidal
  obtain ⟨model, swap, _hn, hsigned, hβ, κ', hκ', hm'⟩ := hS
  obtain ⟨κ, hκ, hm⟩ := hcanonical
  have hκeq (P Q : CochainComplex (ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ) : κ P Q = κ' P Q := by
    apply Iso.ext
    apply HomologicalComplex.hom_ext
    intro n
    apply HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := P) (K₂ := Q)
      (F := ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (c := .up ℤ)
    intro p q hpq
    change p + q = n at hpq
    apply Mod.tensorLeft_obj_hom_ext
    simpa only [Mod.comp_hom', Category.assoc] using
      (hκ P Q p q n hpq (by omega)).trans (hκ' P Q p q n hpq (by omega)).symm
  have hmodels (P Q : CochainComplex (ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
      (hP : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P)
      (hQ : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber Q) :
      ordinaryModel P Q hP = model P Q hP := by
    apply Iso.ext
    have h := hm P Q hP hQ
    rw [hκeq P Q] at h
    exact eq_of_heq (h.trans (hm' P Q hP hQ).symm)
  let F := nativeForget k₀ l X
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  let C := U.mapHomologicalComplex (.up ℤ)
  let := nativeWeilRingedMonoidal b SB
  let := nativeWeilRingedSymmetric b SB βB
  let := S.monoidal
  let := β
  have hs (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hP : NativeTensorKFlat k₀ l X T P) (hQ : NativeTensorKFlat k₀ l X T Q) :
      F.map (β_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
          t.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) =
        t.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (β_ (F.obj (DerivedCategory.Q.obj P)) (F.obj (DerivedCategory.Q.obj Q))).hom := by
    let Pc := C.obj P
    let Qc := C.obj Q
    let aP := U.mapDerivedCategoryFactors.app P
    let aQ := U.mapDerivedCategoryFactors.app Q
    have hPc := native_weil_tensor_forget_kflat k₀ l X T chain P hP
    have hQc := native_weil_tensor_forget_kflat k₀ l X T chain Q hQ
    let n := F.mapIso (nativeWeilRingedTensorModel b T adj A SB TB βB cB Q P hQ) ≪≫
      U.mapDerivedCategoryFactors.app (CochainComplex.mapBifunctor Q P T) ≪≫
      DerivedCategory.Q.mapIso (chain Q P)
    let n' := F.mapIso (nativeWeilRingedTensorModel b T adj A SB TB βB cB P Q hP) ≪≫
      U.mapDerivedCategoryFactors.app (CochainComplex.mapBifunctor P Q T) ≪≫
      DerivedCategory.Q.mapIso (chain P Q)
    let o := S.tensor.mapIso (aP.prod aQ) ≪≫ ordinaryModel Qc Pc hQc
    let o' := S.tensor.mapIso (aQ.prod aP) ≪≫ ordinaryModel Pc Qc hPc
    apply braiding_of_models F t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
      n n' o o' (DerivedCategory.Q.map (swap Qc Pc).hom)
    · exact hforget Q P hQ
    · exact hforget P Q hP
    · simpa only [n, n', Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
        Category.assoc] using native_weil_tensor_ringed_swap_localization
          k₀ l X T adj e he chain hchain b A SB TB βB cB swap hsigned P Q hP hQ
    · have hb : (β_ (DerivedCategory.Q.obj Pc) (DerivedCategory.Q.obj Qc)).hom ≫
          (ordinaryModel Pc Qc hPc).hom =
            (ordinaryModel Qc Pc hQc).hom ≫ DerivedCategory.Q.map (swap Qc Pc).hom := by
        simpa only [hmodels Pc Qc hPc hQc, hmodels Qc Pc hQc hPc] using hβ Qc Pc hQc hPc
      exact braiding_model_of_iso aP aQ (ordinaryModel Qc Pc hQc)
        (ordinaryModel Pc Qc hPc) (DerivedCategory.Q.map (swap Qc Pc).hom) hb
  let K : ObjectProperty (CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :=
    NativeTensorKFlat k₀ l X T
  let q := K.ι ⋙ DerivedCategory.Q
  let W := (HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)).inverseImage K.ι
  let : q.IsLocalization W := A.localization
  let : q.EssSurj := Localization.essSurj q W
  have hsall (P Q : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
      F.map (β_ P Q).hom ≫ t.hom.app (Q, P) =
        t.hom.app (P, Q) ≫ (β_ (F.obj P) (F.obj Q)).hom := by
    exact braiding_of_iso F t (q.objObjPreimageIso P) (q.objObjPreimageIso Q)
      (hs (q.objPreimage P).obj (q.objPreimage Q).obj
        (q.objPreimage P).property (q.objPreimage Q).property)
  refine ⟨ε, ?_, hs⟩
  intro P hP
  refine ⟨hl P hP, ?_⟩
  simpa only [CoefficientClosedStructure.tensor, tensor_map, Functor.prod_obj, F] using
    right_unit_of_left F t ε (DerivedCategory.Q.obj P)
      (by
        simpa only [CoefficientClosedStructure.tensor, tensor_map, Functor.prod_obj, F]
          using hl P hP)
      (hsall (DerivedCategory.Q.obj P) (𝟙_ (DerivedCategory (ProEtaleWeilSheaf k₀ l X))))

end AlgebraicGeometry.ProEtaleWeilSheaf
