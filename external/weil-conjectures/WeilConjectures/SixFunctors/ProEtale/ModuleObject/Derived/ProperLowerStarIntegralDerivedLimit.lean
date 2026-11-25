/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Existence
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Representable
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarIntegersModPowReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarIntegralReductionLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.IntegralCriterion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.ReductionTower

/-!
# The proper direct image on `Dᵇc(-)⟦𝒪̲_E⟧` is a left adjoint: the derived limit

Let `p : Z ⟶ Y` be a proper morphism of separated `k`-schemes of finite type, over any field `k`
of characteristic `≠ ℓ`, and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`. Following the blueprint
proof of `theorem-exceptional-inverse-image--15`, the right adjoint of
`Rp_* : Dᵇc(Z)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` is the derived limit of the torsion-level exceptional inverse
images:

* on each level `𝒪_E ⧸ ℓⁿ`, `Rp_*` followed by the reduction has a right adjoint
  (`isLeftAdjoint_boundedConstructibleLowerStar_comp_integersModPowReduction`), so
  `A ↦ Hom(Rp_* A, Res (L ⧸ ℓⁿ))` is represented on `Dᵇc(Z)⟦𝒪̲_E⟧` by an object `Tₙ`;
* a bounded constructible `L` is derived complete, hence the homotopy limit of the tower
  `L ⧸ ℓⁿ` (`ProEtale.isHomotopyLimit_reductionTowerCone`);
* the `Tₙ` form a tower, and its homotopy limit `G` represents `A ↦ Hom(Rp_* A, L)` on
  `Dᵇc(Z)⟦𝒪̲_E⟧` (`CategoryTheory.Functor.RepresentsOn.exists_of_isHomotopyLimit`), `Rp_*`
  being a right adjoint and hence commuting with products;
* `G` is bounded constructible (`boundedConstructible_homotopyLimit_of_representsOn`).

So `A ↦ Hom(Rp_* A, L)` is representable on `Dᵇc(Z)⟦𝒪̲_E⟧` for every `L`, and `Rp_*` is a left
adjoint (`isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj_of_isProper'`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Pretriangulated

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (p : Z ⟶ Y) [IsProper p.left]

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [IsProper p.left] in
/-- The first derived reduction of the derived limit: if `G` is the homotopy limit of a tower `Tₙ`
of bounded constructible `𝒪_E`-complexes on `Z` representing
`A ↦ Hom(Rp_* A, Res (L ⧸ ℓⁿ⁺¹))` on `Dᵇc(Z)⟦𝒪̲_E⟧`, compatibly with the reduction tower of
`L ∈ Dᵇc(Y)⟦𝒪̲_E⟧`, then `G ⊗ᴸ 𝔽_E` lies in `Dᵇc(Z, 𝔽_E)`. -/
theorem boundedConstructible_derivedReduction_homotopyLimit_of_representsOn
    (L : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    {T : ℕᵒᵖ ⥤ DerivedCategory (Mod (Sheaf (ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z.left))}
    (hT : ∀ n, boundedConstructible _ (T.obj (op n)))
    (ε : T ⋙ (lowerStar (Profinite.padicIntegersRingObj ℓ E.1) p.left).rightDerivedFunctor ⟶
      ProEtale.reductionTower E L.obj)
    (hε : ∀ n,
      ((lowerStar (Profinite.padicIntegersRingObj ℓ E.1) p.left).rightDerivedFunctor).RepresentsOn
      (boundedConstructible _) (ε.app (op n)))
    {c : Cone T} (hc : IsHomotopyLimit c) :
    ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Z.left
      ((derivedReduction Z.left ℓ E).obj c.pt) := by
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : IsNoetherian Z.left := ⟨⟩
  exact boundedConstructible_derivedReduction_of_integersModReduction
    (boundedConstructible_integersModReduction_homotopyLimit p.left L.obj hT ε hε hc)

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] [IsProper p.left] in
/-- The bounded constructible complexes detect the derived limit: if `G` is the homotopy limit
of a tower `Tₙ` of bounded constructible `𝒪_E`-complexes on `Z` representing
`A ↦ Hom(Rp_* A, Res (L ⧸ ℓⁿ⁺¹))` on `Dᵇc(Z)⟦𝒪̲_E⟧`, compatibly with the reduction tower of
`L ∈ Dᵇc(Y)⟦𝒪̲_E⟧`, then `G` is bounded constructible. -/
theorem boundedConstructible_homotopyLimit_of_representsOn
    (L : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    {T : ℕᵒᵖ ⥤ DerivedCategory (Mod (Sheaf (ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z.left))}
    (hT : ∀ n, boundedConstructible _ (T.obj (op n)))
    (ε : T ⋙ (lowerStar (Profinite.padicIntegersRingObj ℓ E.1) p.left).rightDerivedFunctor ⟶
      ProEtale.reductionTower E L.obj)
    (hε : ∀ n,
      ((lowerStar (Profinite.padicIntegersRingObj ℓ E.1) p.left).rightDerivedFunctor).RepresentsOn
      (boundedConstructible _) (ε.app (op n)))
    {c : Cone T} (hc : IsHomotopyLimit c) :
    boundedConstructible _ c.pt := by
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : IsNoetherian Z.left := ⟨⟩
  refine boundedConstructible_of_derivedCompleteIntegers ?_
    (boundedConstructible_derivedReduction_homotopyLimit_of_representsOn ℓ E p L hT ε hε hc)
  obtain ⟨P, hP, δ, hTr⟩ := hc
  have hP' : derivedCompleteIntegers ℓ E Z.left P.pt :=
    derivedCompleteIntegers_of_iso (derivedCompleteIntegers_piObj _
      fun n ↦ derivedCompleteIntegers_of_boundedConstructible (hT n))
      (IsLimit.conePointUniqueUpToIso (limit.isLimit _) hP)
  exact derivedCompleteIntegers_ext₂ _ (inv_rot_of_distTriang _ hTr)
    (derivedCompleteIntegers_shift hP' (-1)) hP'

/-- For a proper `p` and `L ∈ Dᵇc(Y)⟦𝒪̲_E⟧`, the functor `A ↦ Hom(Rp_* A, L)` on `Dᵇc(Z)⟦𝒪̲_E⟧` is
represented by an object of `Dᵇc(Z)⟦𝒪̲_E⟧`. -/
theorem exists_bijective_boundedConstructibleLowerStar_padicIntegersRingObj
    (L : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    ∃ (G : Dᵇc(Z.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
      (e : (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E.1 p).obj G ⟶ L),
      ∀ A, Function.Bijective
        (fun f : A ⟶ G ↦
          (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E.1 p).map f ≫ e) := by
  let Φ := (lowerStar (Profinite.padicIntegersRingObj ℓ E.1) p.left).rightDerivedFunctor
  let P := boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z.left)
  let F := PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E.1 p
  have hY := restrictScalarsIntegersModPowBoundedConstructible (ℓ := ℓ) (E := E.1)
  -- From a representation on `Dᵇc`, a representation for the ambient `Rp_*`.
  have hrep {T : Dᵇc(Z.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧}
      {M : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧} (ε : F.obj T ⟶ M)
      (h : ∀ A, Function.Bijective (fun f : A ⟶ T ↦ F.map f ≫ ε)) :
      Φ.RepresentsOn P ε.hom := by
    intro A hA
    let e₁ : (A ⟶ T.obj) ≃ ((⟨A, hA⟩ : P.FullSubcategory) ⟶ T) :=
      ⟨fun f ↦ ObjectProperty.homMk f, fun f ↦ f.hom, fun _ ↦ rfl, fun _ ↦ rfl⟩
    let e₂ : (F.obj ⟨A, hA⟩ ⟶ M) ≃ (Φ.obj A ⟶ M.obj) :=
      ⟨fun f ↦ f.hom, fun f ↦ ObjectProperty.homMk f, fun _ ↦ rfl, fun _ ↦ rfl⟩
    exact e₂.bijective.comp ((h _).comp e₁.bijective)
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Y.left := ⟨⟩
  have hL : derivedCompleteIntegers ℓ E Y.left L.obj :=
    derivedCompleteIntegers_of_boundedConstructible L.2
  choose T ε hε using fun n : ℕ ↦
    exists_bijective_boundedConstructibleLowerStar_comp_integersModPowRestriction ℓ E.1 (n + 1)
      p (hY (n + 1) Y.left)
      ((boundedConstructibleIntegersModPowReduction Y.left ℓ E.1 (n + 1)).obj L)
  let M := ProEtale.reductionTower E L.obj
  have hεΦ : ∀ n, Φ.RepresentsOn P (M := M.obj (op n)) (ε n).hom := fun n ↦ hrep _ (hε n)
  let Ttower := Functor.RepresentsOn.tower (Φ := Φ) (P := P) (T := fun n ↦ (T n).obj) (M := M)
    (fun n ↦ (T n).2) hεΦ
  let επ := Functor.RepresentsOn.towerπ (Φ := Φ) (P := P) (T := fun n ↦ (T n).obj) (M := M)
    (fun n ↦ (T n).2) hεΦ
  have hεπ : ∀ n, Φ.RepresentsOn P (επ.app (op n)) := fun n ↦ hεΦ n
  obtain ⟨e, -, he⟩ := Functor.RepresentsOn.exists_of_isHomotopyLimit επ hεπ
    (isHomotopyLimit_homotopyLimitCone Ttower) (isHomotopyLimit_reductionTowerCone hL)
  have hG : P (homotopyLimit Ttower) :=
    boundedConstructible_homotopyLimit_of_representsOn ℓ E p L (fun n ↦ (T n).2) επ hεπ
      (isHomotopyLimit_homotopyLimitCone Ttower)
  refine ⟨⟨homotopyLimit Ttower, hG⟩, ObjectProperty.homMk e, fun A ↦ ?_⟩
  let e₁ : (A ⟶ (⟨homotopyLimit Ttower, hG⟩ : P.FullSubcategory)) ≃
      (A.obj ⟶ homotopyLimit Ttower) :=
    ⟨fun f ↦ f.hom, fun f ↦ ObjectProperty.homMk f, fun _ ↦ rfl, fun _ ↦ rfl⟩
  let e₂ : (Φ.obj A.obj ⟶ L.obj) ≃ (F.obj A ⟶ L) :=
    ⟨fun f ↦ ObjectProperty.homMk f, fun f ↦ f.hom, fun _ ↦ rfl, fun _ ↦ rfl⟩
  have : (fun f : A ⟶ ⟨homotopyLimit Ttower, hG⟩ ↦ F.map f ≫ ObjectProperty.homMk e) =
      e₂ ∘ (fun f : A.obj ⟶ homotopyLimit Ttower ↦ Φ.map f ≫ e) ∘ e₁ := by funext f; rfl
  rw [this]
  exact e₂.bijective.comp ((he _ A.2).comp e₁.bijective)

/-- Blueprint `theorem-exceptional-inverse-image--15`, for a finite subextension
`E ⊆ ℚ̄_ℓ`: for a proper morphism `g : Z ⟶ Y`, the derived pushforward
`Rg_* : Dᵇc(Z)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` is a left adjoint, over any field `k`. -/
theorem isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj_of_isProper' :
    (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E.1 p).IsLeftAdjoint := by
  let F := PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E.1 p
  choose G e he using exists_bijective_boundedConstructibleLowerStar_padicIntegersRingObj ℓ E p
  let eq : ∀ A L, (F.obj A ⟶ L) ≃ (A ⟶ G L) := fun A L ↦ (Equiv.ofBijective _ (he L A)).symm
  have heq : ∀ A' A L (f : A' ⟶ A) (g : F.obj A ⟶ L), eq A' L (F.map f ≫ g) = f ≫ eq A L g := by
    intro A' A L f g
    apply (Equiv.ofBijective _ (he L A')).injective
    rw [show ∀ x, Equiv.ofBijective _ (he L A') (eq A' L x) = x from
      (Equiv.ofBijective _ (he L A')).apply_symm_apply]
    change F.map f ≫ g = F.map (f ≫ eq A L g) ≫ e L
    rw [F.map_comp, Category.assoc]
    exact congrArg (F.map f ≫ ·) ((Equiv.ofBijective _ (he L A)).apply_symm_apply g).symm
  exact ⟨_, ⟨Adjunction.adjunctionOfEquivRight eq heq⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
