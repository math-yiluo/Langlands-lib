/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ComparisonTowerStratum

/-!
# The sheaf-level integral identification on a stratum for a tower

Let `M : ℕᵒᵖ ⥤ Sh(T_ét, Λ)` be a tower of étale sheaves of `Λ`-modules whose underlying abelian
tower has epimorphic transitions, `L̂ = lim_n ν^* Mₙ` (a limit cone `c`), `g : T ⟶ Y`
quasi-compact and quasi-separated and `j = i ≫ o : S ⟶ Y` a stratum with `i` a closed immersion
into a scheme with noetherian underlying space. If the towers `n ↦ j^* Hᵐ(Rg_* Mₙ)` are
`IsSetFLC` for all `m`, then on the universal cover `p : Ỹ_y ⟶ S`,
`C(-, lim_n Gₙ) ≅ (p ≫ j)^* Rᵏg_* L̂`, `Gₙ` the stalks of `j^* Hᵏ(Rg_* Mₙ)` at the base point
(`AlgebraicGeometry.ProEtale.nonempty_iso_upperStar_rightDerived_moduleTowerStratum`).

This generalises `AlgebraicGeometry.ProEtale.nonempty_iso_upperStar_rightDerived_integersStratum`
from the constant tower `Λ ⧸ ℓⁿ` (where `L̂ = 𝒪_{E,T}`) to towers of reductions of lattices.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {T Y S S' : Scheme.{u}} (g : T ⟶ Y) [QuasiCompact g]
  [QuasiSeparated g] (M : ℕᵒᵖ ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  {c : Cone ((M ⋙ Etale.moduleAbelianForget Λ T) ⋙ ν^*(T)[Ab.{u + 1}])}

/-- `Hᵏ(p^* j^* Rg_* L̂) ≅ (p ≫ j)^* Rᵏg_* L̂`, the pullbacks being exact. -/
noncomputable def homologyUpperStarModuleTowerConeIso (j : S ⟶ Y) (p : S' ⟶ S) (k : ℕ) :
    (DerivedCategory.homologyFunctor _ k).obj
        ((ProEtale.upperStar Ab.{u + 1} p).mapDerivedCategory.obj
          ((ProEtale.upperStar Ab.{u + 1} j).mapDerivedCategory.obj
            (moduleTowerCone g M (c := c)).pt)) ≅
      (p ≫ j)^*[Ab.{u + 1}].obj (((g)_*[Ab.{u + 1}].rightDerived k).obj c.pt) :=
  ((ProEtale.upperStar Ab.{u + 1} p).mapDerivedCategoryHomologyFunctorIso k).symm.app _ ≪≫
    (ProEtale.upperStar Ab.{u + 1} p).mapIso
      (((ProEtale.upperStar Ab.{u + 1} j).mapDerivedCategoryHomologyFunctorIso k).symm.app _ ≪≫
      (ProEtale.upperStar Ab.{u + 1} j).mapIso
        ((ProEtale.lowerStar Ab.{u + 1} g).homologyRightDerivedFunctorObjSingleFunctorIso
          _ k)) ≪≫
    (ProEtale.upperStarComp Ab.{u + 1} p j).symm.app _

variable (hM : ∀ n : ℕ, Epi ((M ⋙ Etale.moduleAbelianForget Λ T).map (homOfLE n.le_succ).op))
  (hc : IsLimit c)

include hM hc in
/-- **The sheaf-level integral identification on the universal covers of a stratum, for a
tower.** For `j = i ≫ o`, `i` a closed immersion into a scheme with noetherian underlying space
and `o` an open immersion, over which all the towers `n ↦ j^* Hᵐ(Rg_* Mₙ)` are `IsSetFLC`, and
the projection `p : Ỹ_y ⟶ S` of a universal cover, `C(-, lim_n Gₙ) ≅ (p ≫ j)^* Rᵏg_* L̂`, `Gₙ`
the (finite) stalks of `j^* Hᵏ(Rg_* Mₙ)` at the base point. -/
theorem nonempty_iso_upperStar_rightDerived_moduleTowerStratum {U : Scheme.{u}}
    [NoetherianSpace U] (i : S ⟶ U) [IsClosedImmersion i] (o : U ⟶ Y) [IsOpenImmersion o]
    (hH : ∀ (m : ℤ) (n : ℕ), IsSetFLC ((Etale.upperStarHomologyRightDerived g (i ≫ o) m).obj
      (M.obj (op n))))
    {Ω : Type u} [Field Ω] (Ũ : Scheme.UniversalCovers S Ω)
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ S) (k : ℕ) :
    let H' := M ⋙ Etale.upperStarHomologyRightDerived g (i ≫ o) k
    let St := (pointSmallEtale (Ũ.pt y ≫ Ũ.proj y)).sheafFiber (A := ModuleCat.{u + 1} Λ)
    have (n : ℕ) : Finite (St.obj (H'.obj (op n))) := (hH k n).finite_sheafFiber _
    Nonempty (ProEtale.continuousMapAddSheaf (Ũ.cover y)
        (ProEtale.towerLimitAddSubgroup (Qs := fun n ↦ DiscreteShrink (St.obj (H'.obj (op n))))
          (fun n ↦ DiscreteShrink.map
            (St.map (H'.map (homOfLE (n.le_add_right 1)).op)).hom.toAddMonoidHom)) ≅
      (Ũ.proj y ≫ i ≫ o)^*[Ab.{u + 1}].obj (((g)_*[Ab.{u + 1}].rightDerived k).obj c.pt)) := by
  intro H' St _
  let V : U.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hij : IsCompl (Set.range i.base) (Set.range V.ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact isCompl_compl
  have : NoetherianSpace V.toScheme := inferInstanceAs (NoetherianSpace (V : Set U))
  obtain ⟨φ⟩ := nonempty_iso_homologyUpperStar_moduleTowerStratum g M hM hc i V.ι hij o Ũ y k
    (hH ((k : ℤ) - 1)) (hH k)
  exact ⟨φ.symm ≪≫ homologyUpperStarModuleTowerConeIso g M (i ≫ o) (Ũ.proj y) k⟩

end AlgebraicGeometry.ProEtale
