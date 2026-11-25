/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.Tensor
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Map
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Tensor

/-!
# Stalks of tensor products of Weil sheaves

The tensor product `F ⊗ G` of a lisse Weil sheaf `F` with a Weil sheaf `G` is the internal hom
`[F^∨, G]` (`AlgebraicGeometry.WeilSheaf.tensorObj`). Its stalk at a geometric point is
`Hom(F^∨_s, G_s)`, with the Frobenius `f ↦ F_G ∘ f ∘ F_{F^∨}⁻¹`: the pairing of stalks
`[F^∨, G]_s × F^∨_s → G_s` induced by the evaluation is perfect since `F^∨` is lisse
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing_of_lisse`), and it is
compatible with the Frobenius since the evaluation is compatible with the Weil structures
(`AlgebraicGeometry.ProEtaleWeilSheaf.ihom_evaluation_str`). Together with
`(F^∨)_s ≅ (F_s)^∨`, this identifies the stalk of `F ⊗ G` with `F_s ⊗ G_s` and its local
Frobenius with the tensor product of the local Frobenii.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.stalkAtTensorObjEquiv`: the stalk of `F ⊗ G` at a geometric point
  is `Hom(F^∨_s, G_s)`.
- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_tensorObj`: the same at a closed point.
- `AlgebraicGeometry.WeilSheaf.stalkAtTensorObjEquivTensor`: `(F ⊗ G)_s ≅ F_s ⊗ G_s`.
- `AlgebraicGeometry.WeilSheaf.stalkTensorObjEquiv`: the same at a closed point.
- `AlgebraicGeometry.WeilSheaf.HasWeightsAtMost.tensorObj`,
  `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.tensorObj`: weights add under tensor
  products; `AlgebraicGeometry.WeilSheaf.hasEigenvalue_stalk_tensorObj` and
  `AlgebraicGeometry.WeilSheaf.exists_of_hasEigenvalue_stalk_tensorObj`: the eigenvalues of the
  local Frobenius of `F ⊗ G` are the products of those of `F` and `G`.
-/

@[expose] public section

universe u v t

open CategoryTheory MonoidalCategory Endofunctor Limits

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- A line on which the Frobenius acts by the scalar `μ` has `μ ≠ 0`. -/
lemma ne_zero_of_frobeniusEnd_eq_smul {M : FrobeniusModule.{u, v} K}
    (hM : Module.finrank K M.carrier = 1) {μ : K} (hμ : M.frobeniusEnd = μ • LinearMap.id) :
    μ ≠ 0 := by
  rintro rfl
  have hb := (Module.finBasisOfFinrankEq K M.carrier hM).ne_zero 0
  rw [← M.frobenius.map_ne_zero_iff] at hb
  exact hb ((LinearMap.congr_fun hμ _).trans (by rw [zero_smul, LinearMap.zero_apply]))

/-- On a line on which the Frobenius acts by the scalar `μ`, the inverse Frobenius acts by
`μ⁻¹`. -/
lemma frobenius_symm_apply_of_finrank_eq_one {M : FrobeniusModule.{u, v} K}
    (hM : Module.finrank K M.carrier = 1) {μ : K} (hμ : M.frobeniusEnd = μ • LinearMap.id)
    (x : M.carrier) : M.frobenius.symm x = μ⁻¹ • x := by
  have hF (y : M.carrier) : M.frobenius y = μ • y := LinearMap.congr_fun hμ y
  refine M.frobenius.injective ?_
  rw [LinearEquiv.apply_symm_apply, map_smul, hF, smul_smul,
    inv_mul_cancel₀ (ne_zero_of_frobeniusEnd_eq_smul hM hμ), one_smul]

/-- If the Frobenius of a line `M` is multiplication by `μ`, then `Hom_K(M, N)` is `N` with the
Frobenius rescaled by `μ⁻¹`, through the evaluation at a basis vector of `M`. -/
noncomputable def linearHomEquivRescale {M N : FrobeniusModule.{u, v} K}
    (hM : Module.finrank K M.carrier = 1) {μ : K} (hμ : M.frobeniusEnd = μ • LinearMap.id) :
    (M.linearHom N).Equiv (N.rescale μ⁻¹) where
  toLinearEquiv := ((Module.finBasisOfFinrankEq K M.carrier hM).constr K).symm ≪≫ₗ
    LinearEquiv.funUnique (Fin 1) K N.carrier
  map_frobenius (f : M.carrier →ₗ[K] N.carrier) := by
    refine Eq.trans ?_ (frobeniusEnd_rescale_apply (M := N)
      (inv_ne_zero (ne_zero_of_frobeniusEnd_eq_smul hM hμ)) _).symm
    calc _ = N.frobenius (f (M.frobenius.symm (Module.finBasisOfFinrankEq K M.carrier hM 0))) :=
          rfl
      _ = μ⁻¹ • N.frobenius (f (Module.finBasisOfFinrankEq K M.carrier hM 0)) := by
          rw [frobenius_symm_apply_of_finrank_eq_one hM hμ, map_smul, map_smul]

end FrobeniusModule

namespace AlgebraicGeometry.ProEtale

open Functor.LaxMonoidal

variable {l : ℕ} [Fact l.Prime] {K : Type u} [Field K] [IsAlgClosed K]

/-- **The stalk of an internal hom out of a lisse sheaf.** For `F` lisse, any sheaf `N` and a
geometric point `s`, the pairing `𝓗om(F, N)_s → Hom(F_s, N_s)` induced by the evaluation is
bijective. -/
theorem IsAdicLisseSheaf.bijective_evaluationPairing_of_lisse {Z : Scheme.{u}}
    {F : AdicSheaf l Z} (hF : IsAdicLisseSheaf F) (N : AdicSheaf l Z) (s : Spec (.of K) ⟶ Z) :
    Function.Bijective (Mod.evaluationPairing (stalkFunctor l s) F N) := by
  obtain ⟨R, hR, h⟩ := hF
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  have hR' : _ ∈ Scheme.precoverage (@WeaklyEtale : MorphismProperty Scheme.{u}) _ :=
    (show Scheme.proetalePrecoverage ≤ Scheme.precoverage @WeaklyEtale from inf_le_right) _ hR
  rw [Scheme.ofArrows_mem_precoverage_iff (@WeaklyEtale : MorphismProperty Scheme.{u})] at hR'
  obtain ⟨i, v, hv⟩ := hR'.1 (s.base (IsLocalRing.closedPoint K))
  have : WeaklyEtale (f i) := hR'.2 i
  obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback (f := f i) (g := s)
    v (IsLocalRing.closedPoint K) hv
  have : WeaklyEtale (pullback.snd (f i) s) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @WeaklyEtale)
      (IsPullback.of_hasPullback (f i) s) ‹_›
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale (pullback.snd (f i) s) p
  have hs : (σ ≫ pullback.fst (f i) s) ≫ f i = s := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
  rw [← hs, bijective_evaluationPairing_comp_iff]
  obtain ⟨n, ⟨e⟩⟩ := h (f i) (.mk i)
  have : IsIso (ε (stalkFunctor l (σ ≫ pullback.fst (f i) s)) ≫
      (stalkFunctor l (σ ≫ pullback.fst (f i) s)).map
        (MonObj.one (X := adicConstantSheaf l (V i)))) :=
    isIso_unitSection (l := l) (σ ≫ pullback.fst (f i) s)
  exact Mod.bijective_evaluationPairing_of_iso_biproduct _ e _

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilCoefficients

variable {l : ℕ} [Fact l.Prime] {M N L : WeilCoefficients.{u} l}

/-- A pairing `M × N → L` of modules over `ULift ℚ̄_ℓ`, as a `ℚ̄_ℓ`-linear map from `M` to the
`ℚ̄_ℓ`-linear maps `N → L`. -/
noncomputable def homLinearMap
    (p : M →ₗ[ULift.{u + 1} (PadicAlgCl l)] N →ₗ[ULift (PadicAlgCl l)] L) :
    (toModuleCat l).obj M →ₗ[PadicAlgCl l]
      ((toModuleCat l).obj N →ₗ[PadicAlgCl l] (toModuleCat l).obj L) where
  toFun (m : M) :=
    { toFun (n : N) := p m n
      map_add' (n n' : N) := map_add (p m) n n'
      map_smul' c (n : N) := map_smul (p m) (ULift.up c : ULift (PadicAlgCl l)) n }
  map_add' (m m' : M) := by
    ext (n : N)
    change p (m + m') n = p m n + p m' n
    rw [map_add, LinearMap.add_apply]
  map_smul' c (m : M) := by
    ext (n : N)
    change p ((ULift.up c : ULift (PadicAlgCl l)) • m) n =
      (ULift.up c : ULift (PadicAlgCl l)) • p m n
    rw [map_smul, LinearMap.smul_apply]

lemma homLinearMap_apply (p : M →ₗ[ULift.{u + 1} (PadicAlgCl l)] N →ₗ[ULift (PadicAlgCl l)] L)
    (m : M) (n : N) : homLinearMap p m n = p m n :=
  rfl

/-- A bijective pairing `M → Hom(N, L)` of modules over `ULift ℚ̄_ℓ` stays bijective as a map to
the `ℚ̄_ℓ`-linear maps. -/
lemma bijective_homLinearMap
    {p : M →ₗ[ULift.{u + 1} (PadicAlgCl l)] N →ₗ[ULift (PadicAlgCl l)] L}
    (hp : Function.Bijective p) : Function.Bijective (homLinearMap p) := by
  refine ⟨fun (m : M) (m' : M) h ↦ hp.1 (LinearMap.ext fun (n : N) ↦ ?_), fun φ ↦ ?_⟩
  · exact LinearMap.congr_fun h n
  · let ψ : N →ₗ[ULift.{u + 1} (PadicAlgCl l)] L :=
      { toFun (n : N) := φ n
        map_add' n n' := φ.map_add n n'
        map_smul' c n := φ.map_smul c.down n }
    obtain ⟨m, hm⟩ := hp.2 ψ
    exact ⟨m, LinearMap.ext fun (n : N) ↦ LinearMap.congr_fun hm n⟩

end AlgebraicGeometry.WeilCoefficients

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

open Functor.LaxMonoidal ProEtale

omit [Fact (ringChar k₀ ≠ l)] in
/-- The evaluation `[A, B] ⊗ A ⟶ B` is compatible with the Weil structures. -/
theorem ProEtaleWeilSheaf.ihom_evaluation_str (A B : ProEtaleWeilSheaf k₀ l X) :
    ((ProEtaleWeilSheaf.ihom k₀ l X A B).str.hom.hom ⊗ₘ A.str.hom.hom) ≫
        Mod.evaluation A.carrier B.carrier =
      μ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[
        WeilCoefficients.{u} l]
          ((ProEtale.AdicSheaf.ihom A.carrier).obj B.carrier).X A.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map
          (Mod.evaluation A.carrier B.carrier) ≫
        B.str.hom.hom := by
  have : (Mod.mapModComap (G :=
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[
      WeilCoefficients.{u} l]) (adicConstantSheafToLowerStar l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)).IsEquivalence :=
    isEquivalence_adicLowerStar l _
  have h := Mod.μ_comp_map_evaluation (adicConstantSheafToLowerStar l
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) A.carrier B.carrier
  have hstr : (ProEtaleWeilSheaf.ihom k₀ l X A B).str.hom.hom =
      ((adicLowerStarCompIhomIso l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
        A.carrier).inv.app B.carrier).hom ≫
      ((Mod.ihomMap A.str.inv).app _).hom ≫
      ((ProEtale.AdicSheaf.ihom A.carrier).map B.str.hom).hom := rfl
  have hφ : A.str.hom.hom ≫ A.str.inv.hom = 𝟙 _ := by
    rw [← Mod.comp_hom', Iso.hom_inv_id, Mod.id_hom']
  rw [hstr, tensorHom_def', comp_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc]
  rw [Mod.evaluation_naturality A.carrier B.str.hom, Mod.evaluation_ihomMap_assoc A.str.inv]
  erw [← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, hφ,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  erw [reassoc_of% h]
  rfl

namespace WeilSheaf

section TensorStalk

variable (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)

/-- The pairing `(F ⊗ G)_s × (F^∨)_s → G_s` of stalks induced by the evaluation
`[F^∨, G] ⊗ F^∨ ⟶ G` intertwines the Frobenius of the stalks. -/
lemma evaluationPairing_stalkAt_tensorObj_frobenius {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    (G : WeilSheaf k₀ l X) (d : ((F.tensorObj G hF).stalkAt s m hs).carrier)
    (x : ((F.dual hF).stalkAt s m hs).carrier) :
    Mod.evaluationPairing (stalkFunctor l s) (F.dual hF).obj.carrier G.obj.carrier
        (((F.tensorObj G hF).stalkAt s m hs).frobenius d)
        (((F.dual hF).stalkAt s m hs).frobenius x) =
      (G.stalkAt s m hs).frobenius
        (Mod.evaluationPairing (stalkFunctor l s) (F.dual hF).obj.carrier G.obj.carrier d x) := by
  have h := stalkPairing_frobenius s m hs _ _ _ _
    (frobeniusPowIso_tensor (F.tensorObj G hF) (F.dual hF) G _
      (ProEtaleWeilSheaf.ihom_evaluation_str (F.dual hF).obj G.obj) m)
  rw [stalkAt_frobenius_eq_stalkFrobeniusIso, stalkAt_frobenius_eq_stalkFrobeniusIso,
    stalkAt_frobenius_eq_stalkFrobeniusIso, Mod.evaluationPairing_apply,
    Mod.evaluationPairing_apply]
  exact ModuleCat.tmul_eq_of_tensorHom_comp h d x

/-- The `ℚ̄_ℓ`-linear isomorphism `(F ⊗ G)_s ≅ Hom((F^∨)_s, G_s)` induced by the evaluation
`[F^∨, G] ⊗ F^∨ ⟶ G`; it is bijective since `F^∨` is lisse
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing_of_lisse`). -/
noncomputable def stalkAtTensorObjLinearEquiv {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    (G : WeilSheaf k₀ l X) :
    ((F.tensorObj G hF).stalkAt s m hs).carrier ≃ₗ[PadicAlgCl l]
      (((F.dual hF).stalkAt s m hs).carrier →ₗ[PadicAlgCl l] (G.stalkAt s m hs).carrier) :=
  LinearEquiv.ofBijective
    (WeilCoefficients.homLinearMap
      (Mod.evaluationPairing (stalkFunctor l s) (F.dual hF).obj.carrier G.obj.carrier))
    (WeilCoefficients.bijective_homLinearMap
      (IsAdicLisseSheaf.bijective_evaluationPairing_of_lisse hF.dual _ s))

lemma stalkAtTensorObjLinearEquiv_apply {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    (G : WeilSheaf k₀ l X) (d : ((F.tensorObj G hF).stalkAt s m hs).carrier)
    (x : ((F.dual hF).stalkAt s m hs).carrier) :
    stalkAtTensorObjLinearEquiv s m hs hF G d x =
      Mod.evaluationPairing (stalkFunctor l s) (F.dual hF).obj.carrier G.obj.carrier d x :=
  rfl

/-- The isomorphism `(F ⊗ G)_s ≅ Hom((F^∨)_s, G_s)` intertwines the Frobenius of `(F ⊗ G)_s`
with `f ↦ F_G ∘ f ∘ F_{F^∨}⁻¹`. -/
lemma stalkAtTensorObjLinearEquiv_frobenius {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    (G : WeilSheaf k₀ l X) (d : ((F.tensorObj G hF).stalkAt s m hs).carrier) :
    stalkAtTensorObjLinearEquiv s m hs hF G (((F.tensorObj G hF).stalkAt s m hs).frobenius d) =
      (G.stalkAt s m hs).frobenius.toLinearMap ∘ₗ stalkAtTensorObjLinearEquiv s m hs hF G d ∘ₗ
        ((F.dual hF).stalkAt s m hs).frobenius.symm.toLinearMap := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := ((F.dual hF).stalkAt s m hs).frobenius.surjective x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, stalkAtTensorObjLinearEquiv_apply,
    stalkAtTensorObjLinearEquiv_apply]
  exact evaluationPairing_stalkAt_tensorObj_frobenius s m hs hF G d y

/-- The isomorphism `(F ⊗ G)_s ≅ Hom((F^∨)_s, G_s)` intertwines the Frobenius of `(F ⊗ G)_s`
with that of the Frobenius module `Hom((F^∨)_s, G_s)`. -/
lemma stalkAtTensorObjLinearEquiv_map_frobenius {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    (G : WeilSheaf k₀ l X) (d : ((F.tensorObj G hF).stalkAt s m hs).carrier) :
    stalkAtTensorObjLinearEquiv s m hs hF G (((F.tensorObj G hF).stalkAt s m hs).frobenius d) =
      (((F.dual hF).stalkAt s m hs).linearHom (G.stalkAt s m hs)).frobenius
        (stalkAtTensorObjLinearEquiv s m hs hF G d) := by
  rw [FrobeniusModule.linearHom_frobenius_apply]
  exact stalkAtTensorObjLinearEquiv_frobenius s m hs hF G d

/-- The stalk of the tensor product `F ⊗ G = [F^∨, G]` at a geometric point is
`Hom(F^∨_s, G_s)` with the Frobenius `f ↦ F_G ∘ f ∘ F_{F^∨}⁻¹`: the pairing of stalks induced by
the evaluation is perfect
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing_of_lisse`) and
compatible with the Frobenius
(`AlgebraicGeometry.WeilSheaf.evaluationPairing_stalkAt_tensorObj_frobenius`). -/
noncomputable def stalkAtTensorObjEquiv {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    (G : WeilSheaf k₀ l X) :
    ((F.tensorObj G hF).stalkAt s m hs).Equiv
      (((F.dual hF).stalkAt s m hs).linearHom (G.stalkAt s m hs)) where
  toLinearEquiv := stalkAtTensorObjLinearEquiv s m hs hF G
  map_frobenius := stalkAtTensorObjLinearEquiv_map_frobenius s m hs hF G
/-- **The stalk of a tensor product is the tensor product of the stalks.** For a lisse Weil
sheaf `F` and a Weil sheaf `G`, the stalk of `F ⊗ G` at a geometric point is `F_s ⊗ G_s`, with
the tensor product of the Frobenii: it is `Hom((F^∨)_s, G_s)`
(`AlgebraicGeometry.WeilSheaf.stalkAtTensorObjEquiv`), `(F^∨)_s = (F_s)^∨`
(`AlgebraicGeometry.WeilSheaf.stalkAtDualEquiv`) and `Hom(V^∨, W) = V ⊗ W`
(`FrobeniusModule.homDualEquiv`). -/
noncomputable def stalkAtTensorObjEquivTensor (F G : WeilSheaf k₀ l X) (hF : F.IsLisse) :
    ((F.tensorObj G hF).stalkAt s m hs).Equiv ((F.stalkAt s m hs).tensor (G.stalkAt s m hs)) :=
  (stalkAtTensorObjEquiv s m hs hF G).tensorOfHomDual (stalkAtDualEquiv s m hs F hF)

/-- The stalks of the constant Weil sheaf `ℚ̄_ℓ` are nonzero: they are generated by the unit
section (`AlgebraicGeometry.ProEtale.isIso_unitSection`). -/
theorem nontrivial_stalkAt_adicConstant :
    Nontrivial ((adicConstant k₀ l X).stalkAt s m hs).carrier := by
  have : Nontrivial (𝟙_ (WeilCoefficients.{u} l)) :=
    inferInstanceAs (Nontrivial (ULift.{u + 1} (PadicAlgCl l)))
  exact @Equiv.nontrivial ((adicConstant k₀ l X).stalkAt s m hs).carrier _
    (asIso (ProEtale.unitSection l s)).toLinearEquiv.symm.toEquiv this

/-- The only eigenvalue of the local Frobenius of the constant Weil sheaf `ℚ̄_ℓ` is `1`. -/
theorem hasEigenvalue_stalkAt_adicConstant_iff {α : PadicAlgCl l} :
    ((adicConstant k₀ l X).stalkAt s m hs).frobeniusEnd.HasEigenvalue α ↔ α = 1 := by
  have hF : ((adicConstant k₀ l X).stalkAt s m hs).frobeniusEnd = 1 := by
    rw [FrobeniusModule.frobeniusEnd, adicConstant_stalkAt_frobenius]
    rfl
  rw [hF]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
    have h0 : (1 - α) • x = 0 := by
      rw [sub_smul, one_smul, ← hx.1, Module.End.one_apply, sub_self]
    exact (sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_right hx.2)).symm
  · rintro rfl
    have := nontrivial_stalkAt_adicConstant (k₀ := k₀) (l := l) s m hs
    obtain ⟨x, hx⟩ := exists_ne (0 : ((adicConstant k₀ l X).stalkAt s m hs).carrier)
    exact Module.End.hasEigenvalue_of_hasEigenvector (x := x)
      (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 (by simp), hx⟩)


end TensorStalk

/-- The stalk of the tensor product `F ⊗ G` of a lisse Weil sheaf `F` and a Weil sheaf `G` at a
closed point `x` is `Hom((F^∨)_x, G_x)`, with the Frobenius `f ↦ F_G ∘ f ∘ F_{F^∨}⁻¹`. -/
theorem nonempty_equiv_stalk_tensorObj {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    (G : WeilSheaf k₀ l X) (x : X.finitePoints) :
    Nonempty (((F.tensorObj G hF).stalk x).Equiv (((F.dual hF).stalk x).linearHom (G.stalk x))) :=
  ⟨stalkAtTensorObjEquiv _ _ _ hF G⟩

/-- The stalk of `F ⊗ G` at a closed point `x` is `F_x̄ ⊗ G_x̄`, with the local Frobenius
`F_x ⊗ G_x` (`FrobeniusModule.frobeniusEnd_tensor`). -/
noncomputable def stalkTensorObjEquiv (F G : WeilSheaf k₀ l X) (hF : F.IsLisse)
    (x : X.finitePoints) :
    ((F.tensorObj G hF).stalk x).Equiv ((F.stalk x).tensor (G.stalk x)) :=
  stalkAtTensorObjEquivTensor _ _ _ F G hF

/-- If `a` is an eigenvalue of the local Frobenius of `F` at `x` and `b` one of `G`, then `a b`
is an eigenvalue of the local Frobenius of `F ⊗ G` at `x`. -/
theorem hasEigenvalue_stalk_tensorObj {F G : WeilSheaf k₀ l X} (hF : F.IsLisse)
    {x : X.finitePoints} {a b : PadicAlgCl l} (ha : (F.stalk x).frobeniusEnd.HasEigenvalue a)
    (hb : (G.stalk x).frobeniusEnd.HasEigenvalue b) :
    ((F.tensorObj G hF).stalk x).frobeniusEnd.HasEigenvalue (a * b) :=
  FrobeniusModule.hasEigenvalue_of_surjective
    (stalkTensorObjEquiv F G hF x).toLinearEquiv.toLinearMap
    (stalkTensorObjEquiv F G hF x).map_frobenius
    (stalkTensorObjEquiv F G hF x).toLinearEquiv.surjective
    (FrobeniusModule.hasEigenvalue_tensor_mul ha hb)

/-- Every eigenvalue of the local Frobenius of `F ⊗ G` at `x` is a product `a b` of an
eigenvalue `a` of that of `F` and an eigenvalue `b` of that of `G`. -/
theorem exists_of_hasEigenvalue_stalk_tensorObj {F G : WeilSheaf k₀ l X} (hF : F.IsLisse)
    {x : X.finitePoints} {μ : PadicAlgCl l}
    (h : ((F.tensorObj G hF).stalk x).frobeniusEnd.HasEigenvalue μ) :
    ∃ a b, (F.stalk x).frobeniusEnd.HasEigenvalue a ∧ (G.stalk x).frobeniusEnd.HasEigenvalue b ∧
      μ = a * b :=
  FrobeniusModule.exists_of_hasEigenvalue_tensor ((stalkTensorObjEquiv F G hF x).hasEigenvalue h)

/-- The residue cardinality `q_x` at a closed point is positive. -/
lemma residueCard_pos (x : X.finitePoints) :
    0 < (X ↘ Spec (CommRingCat.of k₀)).residueCard x.1 :=
  pow_pos Nat.card_pos _

/-- Weights add under tensor products: if `F` (lisse) has weights at most `w` and `G` weights at
most `w'`, then `F ⊗ G` has weights at most `w + w'`. -/
theorem HasWeightsAtMost.tensorObj {ι : PadicAlgCl l →+* ℂ} {F G : WeilSheaf k₀ l X}
    (hF : F.IsLisse) {w w' : ℝ} (hFw : F.HasWeightsAtMost ι w) (hGw : G.HasWeightsAtMost ι w') :
    (F.tensorObj G hF).HasWeightsAtMost ι (w + w') := fun x ↦
  FrobeniusModule.HasWeightsAtMost.of_equiv (stalkTensorObjEquiv F G hF x)
    ((hFw x).tensor (residueCard_pos x) (hGw x))

/-- The tensor product of a lisse Weil sheaf punctually pure of weight `w` and a Weil sheaf
punctually pure of weight `w'` is punctually pure of weight `w + w'`. -/
theorem IsPunctuallyPureOfWeight.tensorObj {ι : PadicAlgCl l →+* ℂ} {F G : WeilSheaf k₀ l X}
    (hF : F.IsLisse) {w w' : ℝ} (hFw : F.IsPunctuallyPureOfWeight ι w)
    (hGw : G.IsPunctuallyPureOfWeight ι w') :
    (F.tensorObj G hF).IsPunctuallyPureOfWeight ι (w + w') := fun x ↦
  FrobeniusModule.IsPureOfWeight.of_equiv (stalkTensorObjEquiv F G hF x)
    ((hFw x).tensor (residueCard_pos x) (hGw x))

end WeilSheaf

end AlgebraicGeometry
