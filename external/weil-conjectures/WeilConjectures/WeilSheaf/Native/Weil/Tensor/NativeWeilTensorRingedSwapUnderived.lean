/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapSummand
public import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRingedTensorUnderivedData
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetChainUncurry
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBridgeData
import WeilConjectures.WeilSheaf.Ordinary.OrdinaryRingedTensorCoherenceData

/-! # The underived swap across the native ringed bridge

Source: Stacks 03EK, 06YU, 0FPT; the binary mate square and the symmetry square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
open CategoryTheory.BraidedCategory
namespace AlgebraicGeometry.ProEtaleWeilSheaf

-- Prove the tensor calculation with abstract monoidal structures, so its proof
-- does not repeatedly reduce the concrete sheafification tensor constructions.
private theorem tensorComparison_binaryMate
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (μ : MonoidalCategory.tensor C ⋙ F ≅
      (F.prod F) ⋙ MonoidalCategory.tensor D)
    {P Q H I : C} {H' : D} (f : Q ⟶ H) (h : F.obj H ⟶ H')
    (ev : H ⊗ P ⟶ I) (ev' : H' ⊗ F.obj P ⟶ F.obj I)
    (he : μ.hom.app (H, P) ≫ (MonoidalCategory.tensor D).map
      (X := (F.obj H, F.obj P)) (Y := (H', F.obj P)) (h, 𝟙 (F.obj P)) ≫ ev' = F.map ev) :
    μ.hom.app (Q, P) ≫ ((F.map f ≫ h) ⊗ₘ 𝟙 (F.obj P)) ≫ ev' =
      F.map ((f ⊗ₘ 𝟙 P) ≫ ev) := by
  have hn := μ.hom.naturality (show (Q, P) ⟶ (H, P) from (f, 𝟙 P))
  change F.map (f ⊗ₘ 𝟙 P) ≫ μ.hom.app (H, P) =
    μ.hom.app (Q, P) ≫ (F.map f ⊗ₘ F.map (𝟙 P)) at hn
  rw [F.map_id] at hn
  change μ.hom.app (H, P) ≫ (h ⊗ₘ 𝟙 (F.obj P)) ≫ ev' = F.map ev at he
  have hc := tensorHom_comp_tensorHom (F.map f) (𝟙 (F.obj P)) h (𝟙 (F.obj P))
  simp only [Category.comp_id] at hc
  rw [Functor.map_comp, ← hc, Category.assoc, ← reassoc_of% hn, he]

private theorem iso_square_from_inverse_mates
    {C : Type*} [Category* C] {X Y Z W : C}
    (a : X ≅ Y) (c : Z ≅ W) (s : X ⟶ Z) (t : Y ⟶ W)
    (h : a.inv ≫ s = t ≫ c.inv) : a.hom ≫ t = s ≫ c.hom := by
  apply (Iso.eq_inv_comp a).mp
  rw [← Category.assoc, h, Category.assoc, c.inv_hom_id, Category.comp_id]

section SiteMates

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

private theorem tensorHomEquiv_eq (P Q I : RingedTensorModules.{u, u, u} J R) :
    SheafOfModules.tensorHomEquiv (R := R) P Q I =
      ZeroClassAux.tensorHomEquiv.{u, u, u} R P Q I := by
  apply Equiv.ext
  intro f
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  apply PresheafOfModules.hom_ext
  intro W
  refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
  rfl

private def binaryMate (P Q I : RingedTensorModules.{u, u, u} J R)
    (f : Q ⟶ SheafOfModules.homObj (R := R) P I) : Q ⊗ P ⟶ I :=
  (β_ Q P).hom ≫ ((SheafOfModules.tensorHomAdjunction R P).homEquiv Q I).symm f

private theorem binaryMate_eq (P Q I : RingedTensorModules.{u, u, u} J R)
    (f : Q ⟶ SheafOfModules.homObj (R := R) P I) :
    binaryMate R P Q I f = (f ⊗ₘ 𝟙 P) ≫
      RingedForgetTensorTransposition.ordinaryEvaluation J R P I := by
  have he : ((SheafOfModules.tensorHomAdjunction R P).homEquiv
      (SheafOfModules.homObj (R := R) P I) I).symm (𝟙 _) =
    (ZeroClassAux.tensorHomEquiv.{u, u, u} R P
      (SheafOfModules.homObj (R := R) P I) I).symm (𝟙 _) := by
    simp only [SheafOfModules.tensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv,
      tensorHomEquiv_eq]
    rfl
  have hn := (SheafOfModules.tensorHomAdjunction R P).homEquiv_naturality_left_symm
    f (𝟙 (SheafOfModules.homObj (R := R) P I))
  simp only [Category.comp_id] at hn
  rw [binaryMate, hn, he]
  dsimp only [RingedForgetTensorTransposition.ordinaryEvaluation]
  change (β_ Q P).hom ≫ (P ◁ f) ≫ _ = _
  rw [← id_tensorHom, ← braiding_naturality_assoc]

private theorem binaryMate_pre (P Q Q' I : RingedTensorModules.{u, u, u} J R)
    (a : Q' ⟶ Q) (f : Q ⟶ SheafOfModules.homObj (R := R) P I) :
    binaryMate R P Q' I (a ≫ f) = (a ⊗ₘ 𝟙 P) ≫ binaryMate R P Q I f := by
  simp only [binaryMate_eq, ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]

set_option linter.unusedSectionVars false in
private theorem binaryMate_post (P Q I I' : RingedTensorModules.{u, u, u} J R)
    (f : Q ⟶ SheafOfModules.homObj (R := R) P I) (a : I ⟶ I') :
    binaryMate R P Q I' (f ≫ SheafOfModules.homObjMap (R := R) (𝟙 P) a) =
      binaryMate R P Q I f ≫ a := by
  dsimp only [binaryMate]
  rw [Category.assoc]
  congr 1
  exact (SheafOfModules.tensorHomAdjunction R P).homEquiv_naturality_right_symm f a

set_option linter.unusedSectionVars false in
private theorem binaryMate_change (P P' Q I : RingedTensorModules.{u, u, u} J R)
    (a : P' ⟶ P) (f : Q ⟶ SheafOfModules.homObj (R := R) P I) :
    binaryMate R P' Q I (f ≫ SheafOfModules.homObjMap (R := R) a (𝟙 I)) =
      (𝟙 Q ⊗ₘ a) ≫ binaryMate R P Q I f := by
  dsimp only [binaryMate]
  have hn : ((SheafOfModules.tensorHomAdjunction R P').homEquiv Q I).symm
      (f ≫ SheafOfModules.homObjMap (R := R) a (𝟙 I)) =
      (a ▷ Q) ≫ ((SheafOfModules.tensorHomAdjunction R P).homEquiv Q I).symm f := by
    simp only [SheafOfModules.tensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
    apply (SheafOfModules.tensorHomEquiv (R := R) P' Q I).injective
    erw [Equiv.apply_symm_apply,
      SheafOfModules.tensorHomEquiv_whiskerRight_comp (R := R),
      Equiv.apply_symm_apply]
  rw [hn, ← Category.assoc, ← tensorHom_id, ← braiding_naturality]
  simp only [Category.assoc]

private theorem binaryMate_iso (P P' Q Q' I I' : RingedTensorModules.{u, u, u} J R)
    (a : P ≅ P') (b : Q ⟶ Q') (c : I ⟶ I')
    (f : Q ⟶ SheafOfModules.homObj (R := R) P I)
    (g : Q' ⟶ SheafOfModules.homObj (R := R) P' I')
    (h : f ≫ SheafOfModules.homObjMap (R := R) a.inv c = b ≫ g) :
    binaryMate R P Q I f ≫ c = (b ⊗ₘ a.hom) ≫ binaryMate R P' Q' I' g := by
  apply (cancel_epi (𝟙 Q ⊗ₘ a.inv)).1
  rw [← binaryMate_post]
  have hm : SheafOfModules.homObjMap (R := R) (𝟙 P) c ≫
      SheafOfModules.homObjMap (R := R) a.inv (𝟙 I') =
      SheafOfModules.homObjMap (R := R) a.inv c := by
    simp only [SheafOfModules.homObjMap_comp_homObjMap, Category.comp_id]
  rw [← binaryMate_change, Category.assoc, hm, h, binaryMate_pre]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    a.inv_hom_id]

end SiteMates

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (adj : T ⊣₂ ihomBifunctor k₀ l X)
  (A : NativeWeilRingedTensorComplexes b T adj)
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

-- Compare the two concrete sheaf tensor constructions in the evaluation square.
private theorem binaryMate_forget
    (P Q I : RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)
    (f : Q ⟶ SheafOfModules.homObj (R := b.R) P I) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
    letI := SheafOfModules.monoidalCategory b.R
    letI := SheafOfModules.isMonoidal_W_independentCoefficients b.Q
    letI := SheafOfModules.monoidalCategory b.Q
    b.underived.tensor.hom.app (Q, P) ≫
        binaryMate b.Q (b.forget.obj P) (b.forget.obj Q) (b.forget.obj I)
          (b.forget.map f ≫ b.underived.hom.hom.app (op P, I)) =
      b.forget.map (binaryMate b.R P Q I f) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients b.R
  let := SheafOfModules.monoidalCategory b.R
  let := SheafOfModules.symmetricCategory b.R
  let := SheafOfModules.isMonoidal_W_independentCoefficients b.Q
  let := SheafOfModules.monoidalCategory b.Q
  let := SheafOfModules.symmetricCategory b.Q
  rw [binaryMate_eq, binaryMate_eq]
  exact tensorComparison_binaryMate b.forget b.underived.tensor f
    (b.underived.hom.hom.app (op P, I)) _ _
    (b.underived.evaluation P I
      (RingedForgetTensorTransposition.ordinaryEvaluation.{u + 1, u + 1, u + 1} b.J b.R P I)
      (RingedForgetTensorTransposition.ordinaryEvaluation.{u + 1, u + 1, u + 1} b.K b.Q
        (b.forget.obj P) (b.forget.obj I))
      (RingedForgetTensorTransposition.ordinaryEvaluation_pure.{u + 1, u + 1, u + 1}
        b.J b.R P I)
      (RingedForgetTensorTransposition.ordinaryEvaluation_pure.{u + 1, u + 1, u + 1}
        b.K b.Q (b.forget.obj P) (b.forget.obj I)))

include he

private theorem binary_square
    (d : NativeOrdinaryRingedTensorUnderivedData b)
    (P Q : ProEtaleWeilSheaf k₀ l X) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
    letI := SheafOfModules.monoidalCategory b.R
    letI := SheafOfModules.isMonoidal_W_independentCoefficients b.Q
    letI := SheafOfModules.monoidalCategory b.Q
    b.forget.map (A.underived P Q).hom ≫
        b.underived.tensor.hom.app (b.native.functor.obj Q, b.native.functor.obj P) ≫
        (b.square.hom.app Q ⊗ₘ b.square.hom.app P) =
      b.square.hom.app ((T.obj P).obj Q) ≫
        b.ordinary.functor.map (e.hom.app (P, Q)) ≫
        (d.underived P.carrier Q.carrier).hom := by
  classical
  let := SheafOfModules.isMonoidal_W_independentCoefficients b.R
  let := SheafOfModules.monoidalCategory b.R
  let := SheafOfModules.symmetricCategory b.R
  let := SheafOfModules.isMonoidal_W_independentCoefficients b.Q
  let := SheafOfModules.monoidalCategory b.Q
  let := SheafOfModules.symmetricCategory b.Q
  let I := (T.obj P).obj Q
  let f := (adj.adj P).homEquiv Q I (𝟙 I)
  have hf : ((adj.adj P).homEquiv Q I).symm f = 𝟙 I :=
    (adj.adj P).homEquiv Q I |>.symm_apply_apply (𝟙 I)
  have ha := A.uncurry P Q I f
  rw [hf, CategoryTheory.Functor.map_id, Category.comp_id] at ha
  change (A.underived P Q).inv =
    binaryMate b.R (b.native.functor.obj P) (b.native.functor.obj Q)
      (b.native.functor.obj I) (b.native.functor.map f ≫
      b.nativeHom.hom.app (op P, I)) at ha
  have ho := d.uncurry P.carrier Q.carrier I.carrier f.hom.f
  have hh := he P Q I f
  rw [hf] at hh
  change e.inv.app (P, Q) ≫ 𝟙 _ = _ at hh
  rw [Category.comp_id] at hh
  rw [← hh] at ho
  change (d.underived P.carrier Q.carrier).inv ≫
      b.ordinary.functor.map (e.inv.app (P, Q)) =
    binaryMate b.Q (b.ordinary.functor.obj P.carrier)
      (b.ordinary.functor.obj Q.carrier) (b.ordinary.functor.obj I.carrier)
      (b.ordinary.functor.map f.hom.f ≫
      b.ordinaryHom.hom.app (op P.carrier, I.carrier)) at ho
  have hs := b.hom_square P I
  have hs' := congrArg (· ≫ b.ordinaryHom.hom.app (op P.carrier, I.carrier)) hs
  simp only [Category.assoc, Iso.inv_hom_id_app] at hs'
  have hn := b.square.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  have hm : (b.forget.map (b.native.functor.map f ≫
      b.nativeHom.hom.app (op P, I)) ≫
      b.underived.hom.hom.app (op (b.native.functor.obj P),
        b.native.functor.obj I)) ≫
      SheafOfModules.homObjMap (R := b.Q) (b.square.inv.app P)
        (b.square.hom.app I) =
    b.square.hom.app Q ≫ (b.ordinary.functor.map f.hom.f ≫
      b.ordinaryHom.hom.app (op P.carrier, I.carrier)) := by
    simp only [Functor.map_comp, Category.assoc]
    erw [hs', ← Category.assoc, hn]
    rfl
  have hb := binaryMate_iso b.Q _ _ _ _ _ _ (b.square.app P)
    (b.square.hom.app Q) (b.square.hom.app I) _ _ hm
  erw [← ho] at hb
  have ht := binaryMate_forget b (b.native.functor.obj P)
    (b.native.functor.obj Q) (b.native.functor.obj I) (b.native.functor.map f ≫
    b.nativeHom.hom.app (op P, I))
  erw [← ha] at ht
  have hv := congrArg (b.underived.tensor.hom.app
    (b.native.functor.obj Q, b.native.functor.obj P) ≫ ·) hb
  erw [← Category.assoc, ht] at hv
  exact iso_square_from_inverse_mates (b.forget.mapIso (A.underived P Q))
    (b.ordinary.functor.mapIso (e.app (P, Q)) ≪≫ d.underived P.carrier Q.carrier)
    (b.square.hom.app I)
    (b.underived.tensor.hom.app (b.native.functor.obj Q, b.native.functor.obj P) ≫
      (b.square.hom.app Q ⊗ₘ b.square.hom.app P))
    (by simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
      Category.assoc, Functor.comp_obj, Functor.uncurry_obj_obj, I] using hv)

private theorem underived_swap_square
    (d : NativeOrdinaryRingedTensorUnderivedData b)
    (P Q : ProEtaleWeilSheaf k₀ l X) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients b.Q
    letI := SheafOfModules.monoidalCategory b.Q
    letI := SheafOfModules.symmetricCategory b.Q
    b.ordinary.functor.map (e.inv.app (Q, P) ≫
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
          (nativeRingedSwapUnderived b T adj A P Q).hom ≫ e.hom.app (P, Q)) ≫
        (d.underived P.carrier Q.carrier).hom =
      (d.underived Q.carrier P.carrier).hom ≫
        (β_ (b.ordinary.functor.obj P.carrier) (b.ordinary.functor.obj Q.carrier)).hom := by
  classical
  let := SheafOfModules.isMonoidal_W_independentCoefficients b.R
  let := SheafOfModules.monoidalCategory b.R
  let := SheafOfModules.symmetricCategory b.R
  let := SheafOfModules.isMonoidal_W_independentCoefficients b.Q
  let := SheafOfModules.monoidalCategory b.Q
  let := SheafOfModules.symmetricCategory b.Q
  let E := b.native.functor
  let O := b.ordinary.functor
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  let s := nativeRingedSwapUnderived b T adj A P Q
  have hs : E.map s.hom ≫ (A.underived P Q).hom =
      (A.underived Q P).hom ≫ (β_ (E.obj P) (E.obj Q)).hom := by
    simp only [E, s, nativeRingedSwapUnderived, Functor.preimageIso_hom,
      Functor.map_preimage, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have h₁ := binary_square b T adj A e he d P Q
  have h₀ := binary_square b T adj A e he d Q P
  have hn := b.square.hom.naturality s.hom
  change b.forget.map (E.map s.hom) ≫ b.square.hom.app ((T.obj P).obj Q) =
    b.square.hom.app ((T.obj Q).obj P) ≫ O.map (U.map s.hom) at hn
  apply (Iso.cancel_iso_hom_left (O.mapIso (e.app (Q, P))) _ _).mp
  apply (Iso.cancel_iso_hom_left (b.square.app ((T.obj Q).obj P)) _ _).mp
  simp only [Functor.mapIso_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [← O.map_comp_assoc, Iso.hom_inv_id_app, O.map_id, Category.id_comp]
  rw [← reassoc_of% hn, ← h₁, ← b.forget.map_comp_assoc, hs]
  simp only [b.forget.map_comp, Category.assoc]
  have hβ := b.underived.coherence.symmetry (E.obj P) (E.obj Q)
  rw [reassoc_of% hβ]
  rw [← braiding_naturality]
  rw [reassoc_of% h₀]
  rfl

/-- The normalized ordinary symmetry determines the native underived swap.
Source: Stacks 03EK, 06YU and 0FPT; the binary mate and tensor symmetry squares.
(blueprint: new-sf-native-weil-ringed-swap-underived).

Proof: compare the two underived tensors by their adjunction mates. The native
uncurrying law, the normalization of e, and the Hom square give the binary square
across restriction. The defining fully faithful preimage of the native swap,
the symmetry square for restriction, and naturality of the bridge square then
identify its image with the ordinary normalized swap. Reflect this equality
through the faithful ordinary equivalence and apply its pure-tensor equation.
No complexes, K-flatness, derived tensor models, or localization are used. -/
theorem nativeRingedSwapUnderived_forget
    (d : NativeOrdinaryRingedTensorUnderivedData b)
    (P Q : ProEtaleWeilSheaf k₀ l X) :
    Mod.tensorπ P.carrier Q.carrier ≫ (e.inv.app (Q, P)).hom ≫
        ((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
          (nativeRingedSwapUnderived b T adj A P Q).hom).hom ≫
        (e.hom.app (P, Q)).hom =
      (β_ P.carrier.X Q.carrier.X).hom ≫ Mod.tensorπ Q.carrier P.carrier := by
  obtain ⟨s, hs, hpure⟩ := bridge_ordinary_tensor_symmetry b d P.carrier Q.carrier
  have h : e.inv.app (Q, P) ≫
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
        (nativeRingedSwapUnderived b T adj A P Q).hom ≫ e.hom.app (P, Q) = s := by
    apply b.ordinary.functor.map_injective
    apply (cancel_mono (d.underived P.carrier Q.carrier).hom).1
    exact (underived_swap_square b T adj A e he d P Q).trans hs.symm
  simpa only [Mod.comp_hom', Category.assoc] using
    (congrArg (fun f ↦ Mod.tensorπ P.carrier Q.carrier ≫ f.hom) h).trans hpure

end AlgebraicGeometry.ProEtaleWeilSheaf
