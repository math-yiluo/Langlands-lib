/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Bidual
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.Adic.InternalHomEvaluation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.MonoidalIso
public import WeilConjectures.WeilSheaf.LisseDuality

/-!
# Pullback of the internal hom out of a lisse sheaf

For any morphism `g : Z ⟶ Y` and sheaves `M`, `N` of `ℚ̄_ℓ,Y`-modules there is a comparison
morphism `g^* 𝓗om(M, N) ⟶ 𝓗om(g^* M, g^* N)`
(`AlgebraicGeometry.ProEtale.adicUpperStarIhomComparison`), adjoint to
`g^* 𝓗om(M, N) ⊗ g^* M ≅ g^*(𝓗om(M, N) ⊗ M) ⟶ g^* N`. It is natural in both variables and
compatible with the evaluations. For `g` weakly étale it is the isomorphism
`AlgebraicGeometry.ProEtale.adicUpperStarIhomIso`.

If `M` is lisse it is an isomorphism for every `g`
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isIso_adicUpperStarIhomComparison`): after pullback
along the members of the base change of a pro-étale cover trivialising `M`, it becomes the
comparison for a free module of finite rank, which is an isomorphism, being additive in `M` and
an isomorphism for `M = ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {Y' : Scheme.{u}}

attribute [local instance] Sheaf.symmetricCategory

section Comparison

variable {Y Z : Scheme.{u}} (g : Z ⟶ Y)

variable (l) in
/-- The comparison `g^* 𝓗om(M, N) ⟶ 𝓗om(g^* M, g^* N)`, adjoint to
`g^* 𝓗om(M, N) ⊗ g^* M ≅ g^*(𝓗om(M, N) ⊗ M) ⟶ g^* N`. -/
noncomputable def adicUpperStarIhomComparison (M N : AdicSheaf l Y) :
    (g)^*ᵃ[l].obj ((AdicSheaf.ihom M).obj N) ⟶
      (AdicSheaf.ihom ((g)^*ᵃ[l].obj M)).obj ((g)^*ᵃ[l].obj N) :=
  (Mod.ihomAdjunction ((g)^*ᵃ[l].obj M)).homEquiv _ _
    ((adicUpperStarTensorLeftIso l g M).inv.app _ ≫
      (g)^*ᵃ[l].map ((Mod.ihomAdjunction M).counit.app N))

/-- The comparison of the pullback of an internal hom with the internal hom of the pullbacks is
compatible with the evaluations. -/
lemma uncurryHom_adicUpperStarIhomComparison (M N : AdicSheaf l Y) :
    Mod.uncurryHom (adicUpperStarIhomComparison l g M N) =
      μ (g)^*[WeilCoefficients.{u} l] ((AdicSheaf.ihom M).obj N).X M.X ≫
        (g)^*[WeilCoefficients.{u} l].map (Mod.evaluation M N) := by
  have : PreservesColimitsOfShape WalkingParallelPair
      (Mod.mapModComap (G := (g)^*[WeilCoefficients.{u} l]) (adicUpperStarRingHom l g)) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (g)^*ᵃ[l])
  have h₁ := Mod.map_tensorπ_comp_tensorLeftCompMapModComapIso_hom (adicUpperStarRingHom l g)
    (fun _ _ ↦ Adjunction.μ_comp_map_braiding (upperStarLowerStarAdjunction _ g) _ _)
    ((AdicSheaf.ihom M).obj N) M
  have h₃ : Mod.tensorπ ((g)^*ᵃ[l].obj ((AdicSheaf.ihom M).obj N))
      ((g)^*ᵃ[l].obj M) = μ (g)^*[WeilCoefficients.{u} l] _ _ ≫
        (g)^*[WeilCoefficients.{u} l].map (Mod.tensorπ _ M) ≫
          ((adicUpperStarTensorLeftIso l g M).hom.app _).hom := by
    erw [h₁, IsIso.hom_inv_id_assoc]
    rfl
  rw [Mod.uncurryHom_eq, adicUpperStarIhomComparison, Equiv.symm_apply_apply, Mod.comp_hom',
    h₃, Category.assoc, Category.assoc, ← Category.assoc
      ((adicUpperStarTensorLeftIso l g M).hom.app _).hom, ← Mod.comp_hom', Iso.hom_inv_id_app,
    Mod.id_hom', Category.id_comp, adicUpperStar_map_hom, ← Functor.map_comp]
  rfl

/-- The comparison is natural in the target. -/
@[reassoc]
lemma adicUpperStarIhomComparison_naturality (M : AdicSheaf l Y) {N N' : AdicSheaf l Y}
    (f : N ⟶ N') :
    (g)^*ᵃ[l].map ((AdicSheaf.ihom M).map f) ≫ adicUpperStarIhomComparison l g M N' =
      adicUpperStarIhomComparison l g M N ≫
        (AdicSheaf.ihom ((g)^*ᵃ[l].obj M)).map ((g)^*ᵃ[l].map f) := by
  apply Mod.uncurryHom_injective
  rw [Mod.uncurryHom_comp, Mod.uncurryHom_comp_ihom_map, uncurryHom_adicUpperStarIhomComparison,
    uncurryHom_adicUpperStarIhomComparison, adicUpperStar_map_hom, adicUpperStar_map_hom]
  erw [μ_natural_left_assoc]
  rw [← Functor.map_comp, Mod.evaluation_naturality, Functor.map_comp, Category.assoc]

/-- The comparison is natural in the source. -/
@[reassoc]
lemma adicUpperStarIhomComparison_ihomMap {M M' : AdicSheaf l Y} (h : M' ⟶ M)
    (N : AdicSheaf l Y) :
    (g)^*ᵃ[l].map ((Mod.ihomMap h).app N) ≫ adicUpperStarIhomComparison l g M' N =
      adicUpperStarIhomComparison l g M N ≫
        (Mod.ihomMap ((g)^*ᵃ[l].map h)).app ((g)^*ᵃ[l].obj N) := by
  apply Mod.uncurryHom_injective
  rw [Mod.uncurryHom_comp, Mod.uncurryHom_comp_ihomMap, uncurryHom_adicUpperStarIhomComparison,
    uncurryHom_adicUpperStarIhomComparison, adicUpperStar_map_hom, adicUpperStar_map_hom]
  erw [μ_natural_left_assoc]
  rw [← Functor.map_comp, Mod.evaluation_ihomMap, Functor.map_comp]
  exact (μ_natural_right_assoc _ _ _ _).symm

/-- For a weakly étale morphism the comparison is the isomorphism
`AlgebraicGeometry.ProEtale.adicUpperStarIhomIso`. -/
lemma adicUpperStarIhomComparison_eq_of_weaklyEtale [WeaklyEtale g] (M N : AdicSheaf l Y) :
    adicUpperStarIhomComparison l g M N = (adicUpperStarIhomIso l g M).hom.app N := by
  apply Mod.uncurryHom_injective
  rw [uncurryHom_adicUpperStarIhomComparison, Mod.uncurryHom, adicUpperStarIhomIso_evaluation]

/-- The comparison is an isomorphism for a weakly étale morphism. -/
instance isIso_adicUpperStarIhomComparison_of_weaklyEtale [WeaklyEtale g]
    (M N : AdicSheaf l Y) : IsIso (adicUpperStarIhomComparison l g M N) := by
  rw [adicUpperStarIhomComparison_eq_of_weaklyEtale]
  infer_instance

/-- A helper for the evaluation calculus: naturality of `μ` for `g^*` in the first variable,
stated with the underlying sheaves of pulled back modules. -/
@[reassoc]
lemma adicUpperStar_map_hom_whiskerRight_μ {P Q : AdicSheaf l Y} (f : P ⟶ Q)
    (M : AdicSheaf l Y) :
    ((g)^*ᵃ[l].map f).hom ▷ ((g)^*ᵃ[l].obj M).X ≫ μ (g)^*[WeilCoefficients.{u} l] Q.X M.X =
      μ (g)^*[WeilCoefficients.{u} l] P.X M.X ≫
        (g)^*[WeilCoefficients.{u} l].map (f.hom ▷ M.X) :=
  μ_natural_left (g)^*[WeilCoefficients.{u} l] f.hom M.X

/-- The comparison is compatible with the composition of pullbacks. -/
lemma adicUpperStarIhomComparison_comp {W : Scheme.{u}} (r : W ⟶ Z) (M N : AdicSheaf l Y) :
    (adicUpperStarComp l r g).hom.app ((AdicSheaf.ihom M).obj N) ≫
        (r)^*ᵃ[l].map (adicUpperStarIhomComparison l g M N) ≫
          adicUpperStarIhomComparison l r ((g)^*ᵃ[l].obj M) ((g)^*ᵃ[l].obj N) =
      adicUpperStarIhomComparison l (r ≫ g) M N ≫
        (Mod.ihomMap (M := (r)^*ᵃ[l].obj ((g)^*ᵃ[l].obj M))
          ((adicUpperStarComp l r g).inv.app M)).app ((r ≫ g)^*ᵃ[l].obj N) ≫
          (AdicSheaf.ihom ((r)^*ᵃ[l].obj ((g)^*ᵃ[l].obj M))).map
            ((adicUpperStarComp l r g).hom.app N) := by
  apply Mod.uncurryHom_injective
  rw [← Category.assoc (adicUpperStarIhomComparison l (r ≫ g) M N),
    Mod.uncurryHom_comp_ihom_map, Mod.uncurryHom_comp_ihomMap, Mod.uncurryHom_comp,
    Mod.uncurryHom_comp, uncurryHom_adicUpperStarIhomComparison,
    uncurryHom_adicUpperStarIhomComparison, adicUpperStar_map_hom_whiskerRight_μ_assoc,
    ← Functor.map_comp, ← Mod.uncurryHom, uncurryHom_adicUpperStarIhomComparison,
    adicUpperStarComp_hom_app_hom, adicUpperStarComp_inv_app_hom, adicUpperStarComp_hom_app_hom]
  have hm := NatTrans.IsMonoidal.tensor (τ := (upperStarComp (WeilCoefficients.{u} l) r g).hom)
    ((AdicSheaf.ihom M).obj N).X M.X
  rw [Functor.LaxMonoidal.comp_μ] at hm
  have key : (upperStarComp (WeilCoefficients.{u} l) r g).hom.app ((AdicSheaf.ihom M).obj N).X ▷
        (r)^*[WeilCoefficients.{u} l].obj ((g)^*[WeilCoefficients.{u} l].obj M.X) ≫
      μ (r)^*[WeilCoefficients.{u} l]
        ((g)^*[WeilCoefficients.{u} l].obj ((AdicSheaf.ihom M).obj N).X)
        ((g)^*[WeilCoefficients.{u} l].obj M.X) ≫
      (r)^*[WeilCoefficients.{u} l].map
        (μ (g)^*[WeilCoefficients.{u} l] ((AdicSheaf.ihom M).obj N).X M.X ≫
        (g)^*[WeilCoefficients.{u} l].map (Mod.evaluation M N)) =
      ((r ≫ g)^*[WeilCoefficients.{u} l].obj ((AdicSheaf.ihom M).obj N).X ◁
        (upperStarComp (WeilCoefficients.{u} l) r g).inv.app M.X ≫
      μ (r ≫ g)^*[WeilCoefficients.{u} l] ((AdicSheaf.ihom M).obj N).X M.X ≫
        (r ≫ g)^*[WeilCoefficients.{u} l].map (Mod.evaluation M N)) ≫
      (upperStarComp (WeilCoefficients.{u} l) r g).hom.app N.X := by
    rw [Category.assoc, Category.assoc,
      (upperStarComp (WeilCoefficients.{u} l) r g).hom.naturality, reassoc_of% hm, tensorHom_def',
      Category.assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id_app,
      MonoidalCategory.whiskerLeft_id, Category.id_comp, Functor.map_comp]
    rfl
  exact key

/-- The right action of `ℚ̄_ℓ` on a pullback. -/
lemma rightAct_adicUpperStar_obj (N : AdicSheaf l Y) :
    Mod.rightAct ((g)^*ᵃ[l].obj N) =
      ((g)^*ᵃ[l].obj N).X ◁ adicUpperStarRingHom l g ≫
        μ (g)^*[WeilCoefficients.{u} l] N.X (adicConstantSheaf l Y) ≫
          (g)^*[WeilCoefficients.{u} l].map (Mod.rightAct N) := by
  have h := Adjunction.μ_comp_map_braiding (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g)
    N.X (adicConstantSheaf l Y)
  have key : (β_ ((g)^*[WeilCoefficients.{u} l].obj N.X) (adicConstantSheaf l Z)).hom ≫
      adicUpperStarRingHom l g ▷ (g)^*[WeilCoefficients.{u} l].obj N.X ≫
        μ (g)^*[WeilCoefficients.{u} l] (adicConstantSheaf l Y) N.X ≫
          (g)^*[WeilCoefficients.{u} l].map (Mod.act (A := adicConstantSheaf l Y) N.X) =
      (g)^*[WeilCoefficients.{u} l].obj N.X ◁ adicUpperStarRingHom l g ≫
        μ (g)^*[WeilCoefficients.{u} l] N.X (adicConstantSheaf l Y) ≫
          (g)^*[WeilCoefficients.{u} l].map
            ((β_ N.X (adicConstantSheaf l Y)).hom ≫ Mod.act (A := adicConstantSheaf l Y) N.X) := by
    rw [Functor.map_comp, reassoc_of% h, BraidedCategory.braiding_naturality_right_assoc]
  exact key

/-- For `M = ℚ̄_ℓ` the comparison is the identification `g^* 𝓗om(ℚ̄_ℓ, N) ≅ g^* N ≅
𝓗om(ℚ̄_ℓ, g^* N)`. -/
lemma adicUpperStarIhomComparison_unit (N : AdicSheaf l Y) :
    adicUpperStarIhomComparison l g (AdicSheaf.unit l Y) N ≫
        (Mod.ihomMap (adicUpperStarUnitIso l g).inv).app _ =
      (g)^*ᵃ[l].map (Mod.ihomRegularIso.hom.app N) ≫
        Mod.ihomRegularIso.inv.app ((g)^*ᵃ[l].obj N) := by
  apply Mod.uncurryHom_injective
  rw [Mod.uncurryHom_comp_ihomMap, uncurryHom_adicUpperStarIhomComparison, Mod.uncurryHom,
    Mod.evaluation_regular, Mod.evaluation_regular, Mod.comp_hom']
  have key : (g)^*[WeilCoefficients.{u} l].obj ((Mod.ihom (AdicSheaf.unit l Y)).obj N).X ◁
        adicUpperStarRingHom l g ≫
      μ (g)^*[WeilCoefficients.{u} l] ((Mod.ihom (AdicSheaf.unit l Y)).obj N).X
        (adicConstantSheaf l Y) ≫
      (g)^*[WeilCoefficients.{u} l].map
        ((Mod.ihomRegularIso.hom.app N).hom ▷ adicConstantSheaf l Y ≫ Mod.rightAct N) =
      ((g)^*[WeilCoefficients.{u} l].map (Mod.ihomRegularIso.hom.app N).hom ≫
          (Mod.ihomRegularIso.inv.app ((g)^*ᵃ[l].obj N)).hom) ▷ adicConstantSheaf l Z ≫
        (Mod.ihomRegularIso.hom.app ((g)^*ᵃ[l].obj N)).hom ▷ adicConstantSheaf l Z ≫
          Mod.rightAct ((g)^*ᵃ[l].obj N) := by
    rw [← comp_whiskerRight_assoc, Category.assoc, ← Mod.comp_hom', Iso.inv_hom_id_app,
      Mod.id_hom']
    erw [Category.comp_id]
    rw [rightAct_adicUpperStar_obj, Functor.map_comp,
      ← μ_natural_left_assoc, whisker_exchange_assoc]
    rfl
  exact key

/-- The comparison is an isomorphism for `M = ℚ̄_ℓ`. -/
instance isIso_adicUpperStarIhomComparison_unit (N : AdicSheaf l Y) :
    IsIso (adicUpperStarIhomComparison l g (AdicSheaf.unit l Y) N) := by
  have : IsIso ((Mod.ihomMap (adicUpperStarUnitIso l g).inv).app ((g)^*ᵃ[l].obj N)) :=
    Mod.isIso_ihomMap_app _ _
  have : IsIso (adicUpperStarIhomComparison l g (AdicSheaf.unit l Y) N ≫
      (Mod.ihomMap (adicUpperStarUnitIso l g).inv).app ((g)^*ᵃ[l].obj N)) := by
    rw [adicUpperStarIhomComparison_unit]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Mod.ihomMap (adicUpperStarUnitIso l g).inv).app ((g)^*ᵃ[l].obj N))

/-- The comparison is an isomorphism for `M` if it is one for a module isomorphic to `M`. -/
lemma isIso_adicUpperStarIhomComparison_of_iso {M M' : AdicSheaf l Y} (e : M' ≅ M)
    (N : AdicSheaf l Y) [IsIso (adicUpperStarIhomComparison l g M N)] :
    IsIso (adicUpperStarIhomComparison l g M' N) := by
  have : IsIso ((Mod.ihomMap e.hom).app N) := Mod.isIso_ihomMap_app _ _
  have : IsIso ((Mod.ihomMap ((g)^*ᵃ[l].map e.hom)).app ((g)^*ᵃ[l].obj N)) :=
    Mod.isIso_ihomMap_app _ _
  have h := adicUpperStarIhomComparison_ihomMap g e.hom N
  have : IsIso ((g)^*ᵃ[l].map ((Mod.ihomMap e.hom).app N) ≫
      adicUpperStarIhomComparison l g M' N) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left ((g)^*ᵃ[l].map ((Mod.ihomMap e.hom).app N)) _

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- The comparison is an isomorphism for a finite direct sum if it is one for each summand. -/
lemma isIso_adicUpperStarIhomComparison_biproduct {n : ℕ} (M : Fin n → AdicSheaf l Y)
    (N : AdicSheaf l Y) [∀ i, IsIso (adicUpperStarIhomComparison l g (M i) N)] :
    IsIso (adicUpperStarIhomComparison l g (⨁ M) N) := by
  refine ⟨∑ i, (Mod.ihomMap ((g)^*ᵃ[l].map (biproduct.ι M i))).app ((g)^*ᵃ[l].obj N) ≫
    inv (adicUpperStarIhomComparison l g (M i) N) ≫
      (g)^*ᵃ[l].map ((Mod.ihomMap (biproduct.π M i)).app N), ?_, ?_⟩
  · rw [Preadditive.comp_sum]
    have (i : Fin n) : adicUpperStarIhomComparison l g (⨁ M) N ≫
        (Mod.ihomMap ((g)^*ᵃ[l].map (biproduct.ι M i))).app ((g)^*ᵃ[l].obj N) ≫
          inv (adicUpperStarIhomComparison l g (M i) N) ≫
            (g)^*ᵃ[l].map ((Mod.ihomMap (biproduct.π M i)).app N) =
        (g)^*ᵃ[l].map ((Mod.ihomMap (biproduct.ι M i)).app N ≫
          (Mod.ihomMap (biproduct.π M i)).app N) := by
      rw [← adicUpperStarIhomComparison_ihomMap_assoc, IsIso.hom_inv_id_assoc,
        Functor.map_comp]
    simp_rw [this]
    rw [← Functor.map_sum]
    simp_rw [← NatTrans.comp_app]
    rw [← NatTrans.app_sum, Mod.sum_ihomMap_ι_comp_ihomMap_π]
    exact (g)^*ᵃ[l].map_id _
  · rw [Preadditive.sum_comp]
    have (i : Fin n) : ((Mod.ihomMap ((g)^*ᵃ[l].map (biproduct.ι M i))).app ((g)^*ᵃ[l].obj N) ≫
          inv (adicUpperStarIhomComparison l g (M i) N) ≫
            (g)^*ᵃ[l].map ((Mod.ihomMap (biproduct.π M i)).app N)) ≫
          adicUpperStarIhomComparison l g (⨁ M) N =
        (Mod.ihomMap ((g)^*ᵃ[l].map (biproduct.π M i ≫ biproduct.ι M i))).app
          ((g)^*ᵃ[l].obj N) := by
      rw [Category.assoc, Category.assoc, adicUpperStarIhomComparison_ihomMap,
        IsIso.inv_hom_id_assoc, ← NatTrans.comp_app, ← Mod.ihomMap_comp, Functor.map_comp]
    simp_rw [this]
    rw [← NatTrans.app_sum]
    have h : ∑ i, Mod.ihomMap ((g)^*ᵃ[l].map (biproduct.π M i ≫ biproduct.ι M i)) =
        Mod.ihomMapAddHom _ _ ((g)^*ᵃ[l].map (∑ i, biproduct.π M i ≫ biproduct.ι M i)) := by
      rw [Functor.map_sum, map_sum]
      rfl
    rw [h, biproduct.total, CategoryTheory.Functor.map_id, Mod.ihomMapAddHom_apply,
      Mod.ihomMap_id]
    rfl

end Comparison

/-- **Isomorphisms are local for the pro-étale topology**: a morphism of sheaves of
`ℚ̄_ℓ,X`-modules is an isomorphism if its pullbacks along the members of a pro-étale cover are. -/
lemma AdicSheaf.isIso_of_isIso_upperStar {X : Scheme.{u}} {ι : Type*} {W : ι → Scheme.{u}}
    (p : ∀ i, W i ⟶ X) [∀ i, WeaklyEtale (p i)]
    (hp : Presieve.ofArrows W p ∈ Scheme.proetalePrecoverage X) {M N : AdicSheaf l X}
    (f : M ⟶ N) (h : ∀ i, IsIso ((p i)^*ᵃ[l].map f)) : IsIso f := by
  have : Mono f := Preadditive.mono_of_isZero_kernel f
    (AdicSheaf.isZero_of_isZero_upperStar p hp fun i ↦
      (isZero_kernel_of_mono ((p i)^*ᵃ[l].map f)).of_iso (PreservesKernel.iso (p i)^*ᵃ[l] f))
  have : Epi f := Preadditive.epi_of_isZero_cokernel f
    (AdicSheaf.isZero_of_isZero_upperStar p hp fun i ↦
      (isZero_cokernel_of_epi ((p i)^*ᵃ[l].map f)).of_iso (PreservesCokernel.iso (p i)^*ᵃ[l] f))
  exact isIso_of_mono_of_epi f

/-- In a commutative square `a ≫ b ≫ c = d ≫ e ≫ f` of which all sides but `b` are
isomorphisms, so is `b`. -/
private lemma isIso_of_comp_comp_eq {C : Type*} [Category C] {P Q R S Q' R' : C} (a : P ⟶ Q)
    (b : Q ⟶ R) (c : R ⟶ S) (d : P ⟶ Q') (e : Q' ⟶ R') (f : R' ⟶ S) [IsIso a] [IsIso c]
    [IsIso d] [IsIso e] [IsIso f] (h : a ≫ b ≫ c = d ≫ e ≫ f) : IsIso b := by
  have : IsIso (a ≫ b ≫ c) := by
    rw [h]
    infer_instance
  have : IsIso (b ≫ c) := IsIso.of_isIso_comp_left a _
  exact IsIso.of_isIso_comp_right b c

/-- In a commutative square `a ≫ b ≫ c = d ≫ e ≫ f` of which all sides but `d` are
isomorphisms, so is `d`. -/
private lemma isIso_of_comp_comp_eq' {C : Type*} [Category C] {P Q R S Q' R' : C} (a : P ⟶ Q)
    (b : Q ⟶ R) (c : R ⟶ S) (d : P ⟶ Q') (e : Q' ⟶ R') (f : R' ⟶ S) [IsIso a] [IsIso b]
    [IsIso c] [IsIso e] [IsIso f] (h : a ≫ b ≫ c = d ≫ e ≫ f) : IsIso d := by
  have : IsIso (d ≫ e ≫ f) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right d (e ≫ f)

/-- **The pullback of the internal hom out of a lisse sheaf is the internal hom out of the
pullback**: for `M` lisse the comparison `g^* 𝓗om(M, N) ⟶ 𝓗om(g^* M, g^* N)` is an
isomorphism, for every morphism `g`. -/
theorem IsAdicLisseSheaf.isIso_adicUpperStarIhomComparison {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    {M : AdicSheaf l Y} (hM : IsAdicLisseSheaf M) (N : AdicSheaf l Y) :
    IsIso (adicUpperStarIhomComparison l g M N) := by
  obtain ⟨R, hR, hRM⟩ := hM
  obtain ⟨κ, V, v, rfl⟩ := R.exists_eq_ofArrows
  have hv (k : κ) : WeaklyEtale (v k) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk k)
  have hp (k : κ) : WeaklyEtale (pullback.fst g (v k)) :=
    MorphismProperty.pullback_fst _ _ (hv k)
  refine AdicSheaf.isIso_of_isIso_upperStar (fun k ↦ pullback.fst g (v k))
    (Precoverage.mem_coverings_of_isPullback v hR g _ _
      fun k ↦ IsPullback.of_hasPullback g (v k)) _ fun k ↦ ?_
  obtain ⟨n, ⟨e⟩⟩ := hRM (v k) (.mk k)
  have hq (N' : AdicSheaf l (V k)) : IsIso (adicUpperStarIhomComparison l
      (pullback.snd g (v k)) ((v k)^*ᵃ[l].obj M) N') := by
    have := isIso_adicUpperStarIhomComparison_biproduct (pullback.snd g (v k))
      (fun _ : Fin n ↦ AdicSheaf.unit l (V k)) N'
    exact isIso_adicUpperStarIhomComparison_of_iso _ e N'
  have hqv : IsIso (adicUpperStarIhomComparison l (pullback.snd g (v k) ≫ v k) M N) := by
    have := Mod.isIso_ihomMap_app
      ((adicUpperStarComp l (pullback.snd g (v k)) (v k)).inv.app M)
      ((pullback.snd g (v k) ≫ v k)^*ᵃ[l].obj N)
    exact isIso_of_comp_comp_eq' _ _ _ _ _ _
      (adicUpperStarIhomComparison_comp (v k) (pullback.snd g (v k)) M N)
  have hpg : IsIso (adicUpperStarIhomComparison l (pullback.fst g (v k) ≫ g) M N) := by
    rw [pullback.condition]
    exact hqv
  have := Mod.isIso_ihomMap_app ((adicUpperStarComp l (pullback.fst g (v k)) g).inv.app M)
    ((pullback.fst g (v k) ≫ g)^*ᵃ[l].obj N)
  exact isIso_of_comp_comp_eq _ _ _ _ _ _
    (adicUpperStarIhomComparison_comp g (pullback.fst g (v k)) M N)

end AlgebraicGeometry.ProEtale
