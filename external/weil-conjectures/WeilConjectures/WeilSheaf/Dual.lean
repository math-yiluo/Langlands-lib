/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Hom
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom
public import WeilConjectures.SixFunctors.ProEtale.Adic.StalkEvaluation
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.Stalk
public import WeilConjectures.WeilSheaf.StalkPairing

/-!
# Internal homs, duals and geometric coinvariants of Weil sheaves

The Frobenius pullback `Fr^* = (Fr⁻¹)_*` of pro-étale sheaves on the geometric fiber `X̄` is a
monoidal autoequivalence, so it commutes with internal homs
(`CategoryTheory.Functor.Monoidal.ihomObjIso`). The internal hom `[A, B]` of two pro-étale
Weil sheaves therefore carries the Weil structure

`Fr^* [A, B] ≅ [Fr^* A, Fr^* B] ≅ [A, B]`

by the inverse of the Weil structure of `A` in the first variable and that of `B` in the
second (`AlgebraicGeometry.ProEtaleWeilSheaf.ihom`).

The dual of a lisse Weil sheaf `F` is the internal hom `F^∨ = [F, ℚ̄_ℓ]` into the constant Weil
sheaf `ℚ̄_ℓ` (`AlgebraicGeometry.WeilSheaf.adicConstant`). A ℚ̄_ℓ-linear morphism between lisse
`ℓ`-adic sheaves is automatically linear over the sheaf of rings `ℚ̄_ℓ,X̄` (it commutes with
restriction to the points of a weakly contractible cover), so this is the dual of `F` as a
locally free `ℚ̄_ℓ,X̄`-module of finite rank. The internal hom is the duality functor only for
lisse `F`: the dual of a general constructible `F` is its Verdier dual, a Weil complex.

The geometric coinvariants of `F` are the dual of the global sections of `F^∨`. For a lisse
`F` on a geometrically connected `X`, with geometric generic fibre `V` a representation of
`π₁(X̄)`, `Γ(X̄, F^∨) = (V^∨)^{π₁(X̄)} = (V_{π₁(X̄)})^∨`, whose dual is the space of coinvariants
`V_{π₁(X̄)}` with the Frobenius induced by `φ`.

## Main declarations

- `AlgebraicGeometry.ProEtaleWeilSheaf.ihom`: the internal hom of pro-étale Weil sheaves.
- `AlgebraicGeometry.WeilSheaf.dual`: the dual `F^∨ = [F, ℚ̄_ℓ]` of a lisse Weil sheaf, with
  the Weil structure `AlgebraicGeometry.WeilSheaf.dualStr`.
- `AlgebraicGeometry.WeilSheaf.geometricCoinvariants`: the geometric coinvariants of a lisse
  Weil sheaf, with the Frobenius induced from the Weil structure.
- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_dual`: the stalks of the dual of a lisse
  Weil sheaf are the duals of its stalks.

The purity of the geometric coinvariants is
`AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_geometricCoinvariants`, in
`WeilConjectures.WeilSheaf.GeometricCoinvariants`.

## TODO

- The quotient map `F_s̄ ↠ geometricCoinvariants F` at a geometric point `s̄`, the dual of
  `AlgebraicGeometry.WeilSheaf.globalSectionsToStalkObj` for `F^∨` composed with
  `(F^∨)_s̄ ≅ (F_s̄)^∨`, together with its compatibility with the Frobenius at closed points.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Endofunctor Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

section Monoidal

/-- The internal hom of two lisse sheaves is lisse: locally it is the internal hom of finite
sums of copies of `ℚ̄_ℓ,X`, and `𝓗om_{ℚ̄_ℓ,X}(ℚ̄_ℓ,X, ℚ̄_ℓ,X) = ℚ̄_ℓ,X`. -/
theorem ProEtale.IsAdicLisseSheaf.ihom {Z : Scheme.{u}}
    {F G : ProEtale.AdicSheaf l Z} (hF : IsAdicLisseSheaf F)
    (hG : IsAdicLisseSheaf G) : IsAdicLisseSheaf ((ProEtale.AdicSheaf.ihom F).obj G) := by
  obtain ⟨R, hR, hRF⟩ := hF
  obtain ⟨R', hR', hR'G⟩ := hG
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  obtain ⟨ι', V', f', rfl⟩ := R'.exists_eq_ofArrows
  refine ⟨_, Precoverage.comp_mem_coverings f hR (fun i j ↦ pullback.fst (f i) (f' j))
    (fun i ↦ Precoverage.mem_coverings_of_isPullback f' hR' (f i) _ _
      fun j ↦ IsPullback.of_hasPullback (f i) (f' j)), ?_⟩
  rintro _ _ ⟨⟨i, j⟩⟩
  have := Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  have := Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR' (.mk j)
  have : WeaklyEtale (pullback.fst (f i) (f' j)) :=
    MorphismProperty.pullback_fst _ _ ‹WeaklyEtale (f' j)›
  have : WeaklyEtale (pullback.fst (f i) (f' j) ≫ f i) :=
    have : MorphismProperty.IsStableUnderComposition
        (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsMultiplicative.toIsStableUnderComposition
    MorphismProperty.comp_mem _ _ _ ‹_› ‹_›
  obtain ⟨n, ⟨e⟩⟩ := hRF (f i) (.mk i)
  obtain ⟨m, ⟨e'⟩⟩ := hR'G (f' j) (.mk j)
  obtain ⟨e₁⟩ := ProEtale.nonempty_upperStar_iso_biproduct (pullback.fst (f i) (f' j))
    ⟨ProEtale.adicUpperStarUnitIso l _⟩ e
  obtain ⟨e₂⟩ := ProEtale.nonempty_upperStar_iso_biproduct (pullback.snd (f i) (f' j))
    ⟨ProEtale.adicUpperStarUnitIso l _⟩ e'
  refine ⟨n * m, ⟨(ProEtale.adicUpperStarIhomIso l (pullback.fst (f i) (f' j) ≫ f i) F).app G ≪≫
    (Mod.ihomMapIso ((ProEtale.adicUpperStarComp l _ _).app F ≪≫ e₁)).symm.app _ ≪≫
    (ProEtale.AdicSheaf.ihom _).mapIso ((ProEtale.adicUpperStarCongr l pullback.condition).app G ≪≫
      (ProEtale.adicUpperStarComp l _ _).app G ≪≫ e₂) ≪≫ Mod.ihomFreeIso n m⟩⟩

/-- The internal hom from a lisse sheaf into a constructible sheaf is constructible: on the
strata of the second sheaf it is the internal hom of two lisse sheaves
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.upperStar_ihom`). -/
theorem ProEtale.IsAdicConstructibleSheaf.ihom_of_isAdicLisseSheaf {Z : Scheme.{u}}
    {F G : ProEtale.AdicSheaf l Z} (hF : IsAdicLisseSheaf F)
    (hG : IsAdicConstructibleSheaf G) :
    IsAdicConstructibleSheaf ((ProEtale.AdicSheaf.ihom F).obj G) := by
  intro x
  obtain ⟨W, j, hj, hx, ι, hι, S, i, hi, hc, hcover, h⟩ := hG x
  have : WeaklyEtale j := inferInstance
  exact ⟨W, j, hj, hx, ι, hι, S, i, hi, hc, hcover, fun k ↦
    ((hF.upperStar j).upperStar_ihom (i k) (h k)).of_iso
      ((ProEtale.adicUpperStar l (i k)).mapIso ((ProEtale.adicUpperStarIhomIso l j F).app G).symm)⟩

variable (k₀ l X) in
/-- The internal hom `𝓗om_{ℚ̄_ℓ,X̄}(A, B)` of two pro-étale Weil sheaves, with the Weil
structure
```
  Fr^* 𝓗om(A, B) ≅ 𝓗om(Fr^* A, Fr^* B) ≅ 𝓗om(A, Fr^* B) ≅ 𝓗om(A, B)
```
given by the compatibility of the pushforward along the automorphism `Fr⁻¹` with internal homs
(`AlgebraicGeometry.ProEtale.adicLowerStarCompIhomIso`), the inverse of the Weil structure of
`A` in the first variable and the Weil structure of `B` in the second. -/
noncomputable def ProEtaleWeilSheaf.ihom (A B : ProEtaleWeilSheaf k₀ l X) :
    ProEtaleWeilSheaf k₀ l X :=
  IsoAlgebra.mk ((ProEtale.AdicSheaf.ihom A.carrier).obj B.carrier)
    ((ProEtale.adicLowerStarCompIhomIso l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv A.carrier).symm.app
        B.carrier ≪≫
      (Mod.ihomMapIso A.str.symm).app _ ≪≫ (ProEtale.AdicSheaf.ihom A.carrier).mapIso B.str)

omit [Fact (ringChar k₀ ≠ l)] in
/-- The Weil structure of the internal hom `[A, B]` is natural in `B`: a morphism `f : B ⟶ B'` of
pro-étale Weil sheaves induces a morphism `[A, B] ⟶ [A, B']` of pro-étale Weil sheaves. All
three constituents of the Weil structure are natural in the second variable. -/
lemma ProEtaleWeilSheaf.ihom_map_comm (A : ProEtaleWeilSheaf k₀ l X)
    {B B' : ProEtaleWeilSheaf k₀ l X} (f : B ⟶ B') :
    (WeilSheaf.frobeniusPullback k₀ l X).map
        ((ProEtale.AdicSheaf.ihom A.carrier).map f.hom.f) ≫
        (ProEtaleWeilSheaf.ihom k₀ l X A B').obj.str =
      (ProEtaleWeilSheaf.ihom k₀ l X A B).obj.str ≫
        (ProEtale.AdicSheaf.ihom A.carrier).map f.hom.f := by
  simp only [ProEtaleWeilSheaf.ihom, IsoAlgebra.mk_obj, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Functor.mapIso_hom, IsoAlgebra.str_hom, Category.assoc]
  have h₁ := (ProEtale.adicLowerStarCompIhomIso l
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
      A.carrier).inv.naturality f.hom.f
  have h₂ := (Mod.ihomMapIso A.str.symm).hom.naturality
    ((WeilSheaf.frobeniusPullback k₀ l X).map f.hom.f)
  simp only [Functor.comp_map] at h₁ h₂
  rw [reassoc_of% h₁, reassoc_of% h₂, ← Functor.map_comp, ← Functor.map_comp]
  congr 3
  exact f.hom.h

variable (k₀ l X) in
/-- The tensor product `B ⊗_{ℚ̄_ℓ,X̄} A` of two pro-étale Weil sheaves, with the Weil structure
```
  Fr^* (B ⊗ A) ≅ Fr^* B ⊗ Fr^* A ≅ Fr^* B ⊗ A ≅ B ⊗ A
```
given by the compatibility of the pushforward along the automorphism `Fr⁻¹` with tensor
products (`AlgebraicGeometry.ProEtale.adicLowerStarTensorLeftIso`) and the Weil structures of `A`
and `B`. -/
noncomputable def ProEtaleWeilSheaf.tensor (A B : ProEtaleWeilSheaf k₀ l X) :
    ProEtaleWeilSheaf k₀ l X :=
  IsoAlgebra.mk ((Mod.tensorLeft A.carrier).obj B.carrier)
    ((ProEtale.adicLowerStarTensorLeftIso l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
          A.carrier).app B.carrier ≪≫
      (Mod.tensorLeftMapIso A.str).app _ ≪≫ (Mod.tensorLeft A.carrier).mapIso B.str)

omit [Fact (ringChar k₀ ≠ l)] in
/-- The Weil structure of the tensor product `B ⊗ A` is natural in `B`. -/
lemma ProEtaleWeilSheaf.tensor_map_comm (A : ProEtaleWeilSheaf k₀ l X)
    {B B' : ProEtaleWeilSheaf k₀ l X} (f : B ⟶ B') :
    (WeilSheaf.frobeniusPullback k₀ l X).map ((Mod.tensorLeft A.carrier).map f.hom.f) ≫
        (ProEtaleWeilSheaf.tensor k₀ l X A B').obj.str =
      (ProEtaleWeilSheaf.tensor k₀ l X A B).obj.str ≫ (Mod.tensorLeft A.carrier).map f.hom.f := by
  simp only [ProEtaleWeilSheaf.tensor, IsoAlgebra.mk_obj, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, IsoAlgebra.str_hom, Category.assoc]
  have h₁ := (ProEtale.adicLowerStarTensorLeftIso l
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
      A.carrier).hom.naturality f.hom.f
  have h₂ := (Mod.tensorLeftMapIso A.str).hom.naturality
    ((WeilSheaf.frobeniusPullback k₀ l X).map f.hom.f)
  simp only [Functor.comp_map] at h₁ h₂
  rw [reassoc_of% h₁, reassoc_of% h₂, ← Functor.map_comp, ← Functor.map_comp]
  congr 3
  exact f.hom.h

variable (k₀ l X) in
/-- The tensor product `- ⊗ A` with a fixed pro-étale Weil sheaf, as a functor. -/
noncomputable def ProEtaleWeilSheaf.tensorFunctor (A : ProEtaleWeilSheaf k₀ l X) :
    ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X where
  obj B := ProEtaleWeilSheaf.tensor k₀ l X A B
  map f := ObjectProperty.homMk ⟨(Mod.tensorLeft A.carrier).map f.hom.f,
    ProEtaleWeilSheaf.tensor_map_comm A f⟩
  map_id _ := ObjectProperty.hom_ext _
    (Algebra.Hom.ext ((Mod.tensorLeft A.carrier).map_id _))
  map_comp _ _ := ObjectProperty.hom_ext _
    (Algebra.Hom.ext ((Mod.tensorLeft A.carrier).map_comp _ _))

end Monoidal

namespace WeilSheaf

/-- The Weil structure of the dual `F^∨ = [F, ℚ̄_ℓ]` of a Weil sheaf `F`, the composite
```
  Fr^* [F, ℚ̄_ℓ] ≅ [Fr^* F, Fr^* ℚ̄_ℓ] ≅ [F, Fr^* ℚ̄_ℓ] ≅ [F, ℚ̄_ℓ]
```
of the comparison `CategoryTheory.Functor.Monoidal.ihomObjIso` for the monoidal equivalence
`Fr^*`, the inverse of the Weil structure `φ : Fr^* F ≅ F` in the first variable and the Weil
structure of the constant Weil sheaf `ℚ̄_ℓ` in the second. -/
noncomputable def dualStr (F : WeilSheaf k₀ l X) :
    (frobeniusPullback k₀ l X).obj
        ((ProEtale.AdicSheaf.ihom F.obj.carrier).obj
          (ProEtaleWeilSheaf.adicConstant k₀ l X).carrier) ≅
      (ProEtale.AdicSheaf.ihom F.obj.carrier).obj
        (ProEtaleWeilSheaf.adicConstant k₀ l X).carrier :=
  (ProEtaleWeilSheaf.ihom k₀ l X F.obj (ProEtaleWeilSheaf.adicConstant k₀ l X)).str

-- TODO(unify): definition-weil-representation
/-- The dual `F^∨ = [F, ℚ̄_ℓ]` of a lisse Weil sheaf: the internal hom into the constant Weil
sheaf `ℚ̄_ℓ`, with the Weil structure `AlgebraicGeometry.WeilSheaf.dualStr`. It is lisse
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.ihom`), hence constructible. -/
noncomputable def dual (F : WeilSheaf k₀ l X) (hF : F.IsLisse) : WeilSheaf k₀ l X where
  obj := ProEtaleWeilSheaf.ihom k₀ l X F.obj (ProEtaleWeilSheaf.adicConstant k₀ l X)
  property := (hF.ihom (ProEtale.isAdicLisseSheaf_adicConstantSheaf _)).isAdicConstructibleSheaf

/-- The dual of a lisse Weil sheaf is lisse. -/
theorem IsLisse.dual {F : WeilSheaf k₀ l X} (hF : F.IsLisse) : (F.dual hF).IsLisse :=
  ProEtale.IsAdicLisseSheaf.ihom hF (ProEtale.isAdicLisseSheaf_adicConstantSheaf _)

-- TODO(unify): definition-weil-representation
/-- The geometric coinvariants of a lisse Weil sheaf `F`: the dual `Γ(X̄, F^∨)^∨` of the global
sections of the dual `F^∨`, with the dual of the Frobenius of
`AlgebraicGeometry.WeilSheaf.globalSections`.

For a lisse `F` on a geometrically connected `X`, with geometric generic fibre `V` a
representation of `π₁(X̄)`, the global sections are
`Γ(X̄, F^∨) = (V^∨)^{π₁(X̄)} = (V_{π₁(X̄)})^∨`, so this is the space of coinvariants
`V_{π₁(X̄)}` with the Frobenius induced from the Weil structure: the maximal geometrically
constant quotient of `F`. If `X̄` is not connected, `Γ(X̄, -)` is a sum over its connected
components.

The universe `max (u + 1) 0 = u + 1` of `FrobeniusModule.dual` agrees with that of the global
sections, since the coefficients `ℚ̄_ℓ` live in universe `0`. -/
noncomputable def geometricCoinvariants [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l X)
    (hF : F.IsLisse) : FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  FrobeniusModule.dual (globalSections (F.dual hF))

section DualStalk

open Functor.LaxMonoidal ProEtale

/-- The evaluation `F^∨ ⊗ F ⟶ ℚ̄_ℓ` is compatible with the Weil structures. -/
theorem dual_evaluation_str (F : WeilSheaf k₀ l X) (hF : F.IsLisse) :
    ((F.dual hF).obj.str.hom.hom ⊗ₘ F.obj.str.hom.hom) ≫
        Mod.evaluation F.obj.carrier (adicConstant k₀ l X).obj.carrier =
      μ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[
          WeilCoefficients.{u} l]
          (F.dual hF).obj.carrier.X F.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map
          (Mod.evaluation F.obj.carrier (adicConstant k₀ l X).obj.carrier) ≫
        (adicConstant k₀ l X).obj.str.hom.hom := by
  have : (Mod.mapModComap
      (G := ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[
      WeilCoefficients.{u} l]) (adicConstantSheafToLowerStar l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)).IsEquivalence :=
    isEquivalence_adicLowerStar l _
  have h := Mod.μ_comp_map_evaluation (adicConstantSheafToLowerStar l
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) F.obj.carrier (adicConstant k₀ l X).obj.carrier
  have hstr : (F.dual hF).obj.str.hom.hom =
      ((adicLowerStarCompIhomIso l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
        F.obj.carrier).inv.app (adicConstant k₀ l X).obj.carrier).hom ≫
      ((Mod.ihomMap F.obj.str.inv).app _).hom ≫
      ((ProEtale.AdicSheaf.ihom F.obj.carrier).map (adicConstant k₀ l X).obj.str.hom).hom := rfl
  have hφ : F.obj.str.hom.hom ≫ F.obj.str.inv.hom = 𝟙 _ := by
    rw [← Mod.comp_hom', Iso.hom_inv_id, Mod.id_hom']
  rw [hstr, tensorHom_def', comp_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc]
  rw [Mod.evaluation_naturality F.obj.carrier (adicConstant k₀ l X).obj.str.hom,
    Mod.evaluation_ihomMap_assoc F.obj.str.inv]
  erw [← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, hφ,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  erw [reassoc_of% h]
  rfl

variable (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)

/-- The pairing `(F^∨)_s × F_s → (ℚ̄_ℓ)_s` of stalks induced by the evaluation is invariant under
the Frobenius of the stalks. -/
lemma evaluationPairing_stalkAt_frobenius (F : WeilSheaf k₀ l X) (hF : F.IsLisse)
    (d : ((F.dual hF).stalkAt s m hs).carrier) (x : (F.stalkAt s m hs).carrier) :
    Mod.evaluationPairing (stalkFunctor l s) F.obj.carrier (adicConstant k₀ l X).obj.carrier
        (((F.dual hF).stalkAt s m hs).frobenius d) ((F.stalkAt s m hs).frobenius x) =
      Mod.evaluationPairing (stalkFunctor l s) F.obj.carrier (adicConstant k₀ l X).obj.carrier
        d x := by
  have h := stalkPairing_frobenius s m hs _ _ _ _
    (frobeniusPowIso_tensor (F.dual hF) F (adicConstant k₀ l X) _ (dual_evaluation_str F hF) m)
  have hA := adicConstant_stalkAt_frobenius (l := l) s m hs
  rw [stalkAt_frobenius_eq_stalkFrobeniusIso] at hA
  rw [stalkAt_frobenius_eq_stalkFrobeniusIso, stalkAt_frobenius_eq_stalkFrobeniusIso,
    Mod.evaluationPairing_apply, Mod.evaluationPairing_apply]
  exact WeilCoefficients.pairing_linearEquivOfIso
    ((stalkFrobeniusIso k₀ l X s m hs).app (F.dual hF).obj.carrier.X ≪≫
      (stalkSheafFunctor k₀ l X s).mapIso
        ((ProEtale.AdicSheaf.forget _).mapIso ((F.dual hF).frobeniusPowIso m)))
    ((stalkFrobeniusIso k₀ l X s m hs).app F.obj.carrier.X ≪≫
      (stalkSheafFunctor k₀ l X s).mapIso
        ((ProEtale.AdicSheaf.forget _).mapIso (F.frobeniusPowIso m)))
    ((stalkFrobeniusIso k₀ l X s m hs).app (adicConstant k₀ l X).obj.carrier.X ≪≫
      (stalkSheafFunctor k₀ l X s).mapIso
        ((ProEtale.AdicSheaf.forget _).mapIso ((adicConstant k₀ l X).frobeniusPowIso m)))
    (μ (stalkSheafFunctor k₀ l X s) _ _)
    ((stalkSheafFunctor k₀ l X s).map
      (Mod.evaluation F.obj.carrier (adicConstant k₀ l X).obj.carrier)) h hA d x

/-- The stalk of the dual of a lisse Weil sheaf at a geometric point is the dual of the stalk,
compatibly with the Frobenius: the pairing of stalks induced by the evaluation is perfect
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing`) and invariant
under the Frobenius (`AlgebraicGeometry.WeilSheaf.evaluationPairing_stalkAt_frobenius`). -/
noncomputable def stalkAtDualEquiv (F : WeilSheaf k₀ l X) (hF : F.IsLisse) :
    ((F.dual hF).stalkAt s m hs).Equiv (F.stalkAt s m hs).dual where
  toLinearEquiv := LinearEquiv.ofBijective
    (WeilCoefficients.dualLinearMap
      (Mod.evaluationPairing (stalkFunctor l s) F.obj.carrier (adicConstant k₀ l X).obj.carrier)
      (asIso (unitSection l s)).symm.toLinearEquiv.toLinearMap)
    (WeilCoefficients.bijective_dualLinearMap
      (IsAdicLisseSheaf.bijective_evaluationPairing hF s)
      (asIso (unitSection l s)).symm.toLinearEquiv)
  map_frobenius d := LinearMap.ext fun x ↦ by
    obtain ⟨y, rfl⟩ := (F.stalkAt s m hs).frobenius.surjective x
    rw [FrobeniusModule.dual_frobenius_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact congrArg (fun z ↦ ((asIso (unitSection l s)).symm.toLinearEquiv z).down)
      (evaluationPairing_stalkAt_frobenius s m hs F hF d y)

end DualStalk

/-- The stalk of the dual of a lisse Weil sheaf is the dual of its stalk: the local Frobenius
of `F^∨` at `x` is the inverse transpose of that of `F`. -/
theorem nonempty_equiv_stalk_dual {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    (x : X.finitePoints) : Nonempty (((F.dual hF).stalk x).Equiv (F.stalk x).dual) :=
  ⟨stalkAtDualEquiv _ _ _ F hF⟩

end WeilSheaf

end AlgebraicGeometry
