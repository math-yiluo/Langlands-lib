/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Symmetric
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Curry
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
public import WeilConjectures.WeilSheaf.StalkTensor

/-!
# The tensor–hom adjunction for pro-étale Weil sheaves

For a pro-étale Weil sheaf `M` on a `k₀`-scheme `X`, the tensor product `- ⊗ M` and the internal
hom `[M, -]` of pro-étale Weil sheaves (`AlgebraicGeometry.ProEtaleWeilSheaf.tensorFunctor` and
`AlgebraicGeometry.ProEtaleWeilSheaf.ihomFunctor`) are adjoint
(`AlgebraicGeometry.ProEtaleWeilSheaf.tensorIhomAdjunction`), with the unit and the counit of the
adjunction `- ⊗ M ⊣ [M, -]` of the underlying sheaves of `ℚ̄_ℓ,X̄`-modules.

Both are checked on underlying sheaves of `ℚ̄_ℓ`-modules, through two compatibilities of the Weil
structures with the Frobenius pullback `Fr^*`, which is lax monoidal:

- the quotient map `P ⊗ M ⟶ P ⊗_{ℚ̄_ℓ} M` intertwines the Weil structures
  (`AlgebraicGeometry.ProEtaleWeilSheaf.tensorπ_str`);
- a morphism `v : P ⟶ [M, N]` is compatible with the Weil structures as soon as its uncurried
  form `P ⊗ M ⟶ N` is (`AlgebraicGeometry.ProEtaleWeilSheaf.map_comp_ihom_str_of_uncurryHom`),
  the evaluation being compatible with the Weil structures
  (`AlgebraicGeometry.ProEtaleWeilSheaf.ihom_evaluation_str`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

namespace AlgebraicGeometry

open ProEtale Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

set_option hygiene false in
/-- The Frobenius pullback `Fr^* = (Fr⁻¹)_*` of sheaves of `ℚ̄_ℓ`-modules on `X̄`. -/
local notation "Fr" =>
  ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u} l]

attribute [local instance] Sheaf.symmetricCategory

namespace ProEtaleWeilSheaf

/-- A morphism of the underlying sheaves of `ℚ̄_ℓ,X̄`-modules of two pro-étale Weil sheaves
which intertwines the Weil structures on underlying sheaves of `ℚ̄_ℓ`-modules is a morphism of
pro-étale Weil sheaves. -/
noncomputable def homMk {P Q : ProEtaleWeilSheaf k₀ l X} (f : P.carrier ⟶ Q.carrier)
    (h : (Fr).map f.hom ≫ Q.str.hom.hom = P.str.hom.hom ≫ f.hom) : P ⟶ Q :=
  ObjectProperty.homMk ⟨f, Mod.hom_ext _ _ h⟩

@[simp]
lemma homMk_hom_f {P Q : ProEtaleWeilSheaf k₀ l X} (f : P.carrier ⟶ Q.carrier)
    (h : (Fr).map f.hom ≫ Q.str.hom.hom = P.str.hom.hom ≫ f.hom) : (homMk f h).hom.f = f :=
  rfl

/-- A morphism of pro-étale Weil sheaves intertwines the Weil structures on underlying sheaves of
`ℚ̄_ℓ`-modules. -/
@[reassoc]
lemma map_hom_comp_str_hom {P Q : ProEtaleWeilSheaf k₀ l X} (f : P ⟶ Q) :
    (Fr).map f.hom.f.hom ≫ Q.str.hom.hom = P.str.hom.hom ≫ f.hom.f.hom :=
  congrArg Mod.Hom.hom f.hom.h

/-- The Weil structure of a pro-étale Weil sheaf is invertible on underlying sheaves. -/
instance isIso_str_hom_hom (P : ProEtaleWeilSheaf k₀ l X) : IsIso P.str.hom.hom :=
  inferInstanceAs (IsIso ((Mod.forget _).map P.str.hom))

/-- **The quotient map `P ⊗ M ⟶ P ⊗_{ℚ̄_ℓ} M` is compatible with the Weil structures.** -/
theorem tensorπ_str (P M : ProEtaleWeilSheaf k₀ l X) :
    (P.str.hom.hom ⊗ₘ M.str.hom.hom) ≫ Mod.tensorπ P.carrier M.carrier =
      μ Fr P.carrier.X M.carrier.X ≫ (Fr).map (Mod.tensorπ P.carrier M.carrier) ≫
        (ProEtaleWeilSheaf.tensor k₀ l X M P).str.hom.hom := by
  have : (Mod.mapModComap (G := Fr) (adicConstantSheafToLowerStar l
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)).IsEquivalence :=
    isEquivalence_adicLowerStar l _
  have h₁ := Mod.map_tensorπ_comp_tensorLeftCompMapModComapIso_hom (adicConstantSheafToLowerStar l
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) P.carrier M.carrier
  have hstr : (ProEtaleWeilSheaf.tensor k₀ l X M P).str.hom.hom =
      ((adicLowerStarTensorLeftIso l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv M.carrier).hom.app
        P.carrier).hom ≫
      ((Mod.tensorLeftMapIso M.str).hom.app _).hom ≫
      ((Mod.tensorLeft M.carrier).map P.str.hom).hom := rfl
  rw [hstr, ← Category.assoc ((Fr).map _)]
  erw [h₁]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  erw [Mod.tensorπ_tensorLeftMap_assoc, Mod.tensorπ_map]
  rw [tensorHom_def', Category.assoc]
  rfl

/-- **A morphism into an internal hom is compatible with the Weil structures if its uncurried
form is.** For pro-étale Weil sheaves `P`, `M`, `N` and a morphism `v : P ⟶ [M, N]` of the
underlying sheaves of `ℚ̄_ℓ,X̄`-modules whose uncurried form `P ⊗ M ⟶ N` intertwines the Weil
structures, `v` intertwines the Weil structures of `P` and of `[M, N]`. -/
theorem map_comp_ihom_str_of_uncurryHom {P M N : ProEtaleWeilSheaf k₀ l X}
    (v : P.carrier ⟶ (AdicSheaf.ihom M.carrier).obj N.carrier)
    (h : (P.str.hom.hom ⊗ₘ M.str.hom.hom) ≫ Mod.uncurryHom v =
      μ Fr P.carrier.X M.carrier.X ≫ (Fr).map (Mod.uncurryHom v) ≫ N.str.hom.hom) :
    (Fr).map v.hom ≫ (ProEtaleWeilSheaf.ihom k₀ l X M N).str.hom.hom = P.str.hom.hom ≫ v.hom := by
  apply Mod.hom_ext_of_evaluation (D := M.carrier)
  rw [← cancel_epi ((Fr).obj P.carrier.X ◁ M.str.hom.hom)]
  have he := ihom_evaluation_str M N
  rw [comp_whiskerRight, Category.assoc, whisker_exchange_assoc, ← tensorHom_def'_assoc]
  erw [he]
  rw [comp_whiskerRight, Category.assoc, whisker_exchange_assoc, ← tensorHom_def_assoc]
  rw [Mod.uncurryHom] at h
  erw [h]
  erw [μ_natural_left_assoc]
  rw [← (Fr).map_comp_assoc]

omit [Finite k₀] in
/-- The uncurried form of the unit `P ⟶ [M, P ⊗ M]` of the tensor–hom adjunction is the quotient
map `P ⊗ M ⟶ P ⊗_{ℚ̄_ℓ} M`. -/
lemma uncurryHom_ihomAdjunction_unit (P M : ProEtale.AdicSheaf l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    Mod.uncurryHom ((Mod.ihomAdjunction M).unit.app P) = Mod.tensorπ P M := by
  rw [Mod.uncurryHom_eq, Adjunction.homEquiv_counit]
  erw [(Mod.ihomAdjunction M).left_triangle_components P]
  exact Category.comp_id _

/-- The unit of the adjunction `- ⊗ M ⊣ [M, -]` of sheaves of `ℚ̄_ℓ,X̄`-modules is compatible with
the Weil structures. -/
lemma map_unit_comp_str (M P : ProEtaleWeilSheaf k₀ l X) :
    (Fr).map ((Mod.ihomAdjunction M.carrier).unit.app P.carrier).hom ≫
        (ProEtaleWeilSheaf.ihom k₀ l X M (ProEtaleWeilSheaf.tensor k₀ l X M P)).str.hom.hom =
      P.str.hom.hom ≫ ((Mod.ihomAdjunction M.carrier).unit.app P.carrier).hom := by
  refine map_comp_ihom_str_of_uncurryHom (N := ProEtaleWeilSheaf.tensor k₀ l X M P) _ ?_
  rw [uncurryHom_ihomAdjunction_unit]
  exact tensorπ_str P M

/-- Two morphisms out of `Fr^*(P ⊗_{ℚ̄_ℓ} M)` agreeing on `Fr^* P ⊗ Fr^* M` are equal. -/
lemma frobeniusPullback_tensor_hom_ext {P M : ProEtaleWeilSheaf k₀ l X}
    {N : ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {f g : (WeilSheaf.frobeniusPullback k₀ l X).obj ((Mod.tensorLeft M.carrier).obj P.carrier) ⟶ N}
    (h : μ Fr P.carrier.X M.carrier.X ≫ (Fr).map (Mod.tensorπ P.carrier M.carrier) ≫ f.hom =
      μ Fr P.carrier.X M.carrier.X ≫ (Fr).map (Mod.tensorπ P.carrier M.carrier) ≫ g.hom) :
    f = g := by
  have : (Mod.mapModComap (G := Fr) (adicConstantSheafToLowerStar l
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)).IsEquivalence :=
    isEquivalence_adicLowerStar l _
  have h₁ := Mod.map_tensorπ_comp_tensorLeftCompMapModComapIso_hom (adicConstantSheafToLowerStar l
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) P.carrier M.carrier
  set T := (adicLowerStarTensorLeftIso l
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv M.carrier).app P.carrier
  have hT : Mod.tensorπ _ _ ≫ T.inv.hom =
      μ Fr P.carrier.X M.carrier.X ≫ (Fr).map (Mod.tensorπ P.carrier M.carrier) := by
    rw [← cancel_mono T.hom.hom, Category.assoc, ← Mod.comp_hom', T.inv_hom_id]
    erw [Mod.id_hom', Category.comp_id]
    rw [Category.assoc]
    erw [h₁]
    simp only [IsIso.hom_inv_id_assoc]
    rfl
  rw [← T.hom_inv_id_assoc f, ← T.hom_inv_id_assoc g]
  congr 1
  refine Mod.tensorLeft_obj_hom_ext ?_
  rw [Mod.comp_hom', Mod.comp_hom', reassoc_of% hT, reassoc_of% hT]
  exact h

/-- The counit `[M, N] ⊗ M ⟶ N` of the adjunction `- ⊗ M ⊣ [M, -]` of sheaves of
`ℚ̄_ℓ,X̄`-modules is compatible with the Weil structures. -/
lemma map_counit_comp_str (M N : ProEtaleWeilSheaf k₀ l X) :
    (WeilSheaf.frobeniusPullback k₀ l X).map ((Mod.ihomAdjunction M.carrier).counit.app
        N.carrier) ≫ N.str.hom =
      (ProEtaleWeilSheaf.tensor k₀ l X M (ProEtaleWeilSheaf.ihom k₀ l X M N)).str.hom ≫
        (Mod.ihomAdjunction M.carrier).counit.app N.carrier := by
  refine frobeniusPullback_tensor_hom_ext (P := ProEtaleWeilSheaf.ihom k₀ l X M N) ?_
  have h := tensorπ_str (ProEtaleWeilSheaf.ihom k₀ l X M N) M
  have he := ihom_evaluation_str M N
  simp only [Mod.comp_hom']
  rw [← reassoc_of% h]
  erw [adicLowerStar_map_hom]
  rw [← (Fr).map_comp_assoc]
  change _ = _ ≫ Mod.evaluation _ _
  erw [he]
  rfl

variable (k₀ l X) in
/-- **The tensor–hom adjunction for pro-étale Weil sheaves**: `- ⊗ M ⊣ [M, -]`, with the unit and
the counit of the adjunction of the underlying sheaves of `ℚ̄_ℓ,X̄`-modules. -/
noncomputable def tensorIhomAdjunction (M : ProEtaleWeilSheaf k₀ l X) :
    ProEtaleWeilSheaf.tensorFunctor k₀ l X M ⊣ ProEtaleWeilSheaf.ihomFunctor k₀ l X M :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app P := homMk ((Mod.ihomAdjunction M.carrier).unit.app P.carrier)
            (map_unit_comp_str M P)
          naturality _ _ f := ObjectProperty.hom_ext _
            (Algebra.Hom.ext ((Mod.ihomAdjunction M.carrier).unit.naturality f.hom.f)) }
      counit :=
        { app N := ObjectProperty.homMk
            ⟨(Mod.ihomAdjunction M.carrier).counit.app N.carrier, map_counit_comp_str M N⟩
          naturality _ _ f := ObjectProperty.hom_ext _
            (Algebra.Hom.ext ((Mod.ihomAdjunction M.carrier).counit.naturality f.hom.f)) }
      left_triangle := by
        ext P
        exact ObjectProperty.hom_ext _ (Algebra.Hom.ext
          ((Mod.ihomAdjunction M.carrier).left_triangle_components P.carrier))
      right_triangle := by
        ext N
        exact ObjectProperty.hom_ext _ (Algebra.Hom.ext
          ((Mod.ihomAdjunction M.carrier).right_triangle_components N.carrier)) }

@[simp]
lemma tensorIhomAdjunction_unit_app_hom_f (M P : ProEtaleWeilSheaf k₀ l X) :
    ((tensorIhomAdjunction k₀ l X M).unit.app P).hom.f =
      (Mod.ihomAdjunction M.carrier).unit.app P.carrier :=
  rfl

@[simp]
lemma tensorIhomAdjunction_counit_app_hom_f (M N : ProEtaleWeilSheaf k₀ l X) :
    ((tensorIhomAdjunction k₀ l X M).counit.app N).hom.f =
      (Mod.ihomAdjunction M.carrier).counit.app N.carrier :=
  rfl

end ProEtaleWeilSheaf

end AlgebraicGeometry
