/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCover
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.LocallyConstantSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LocallyConstantWContractible

/-!
# Finite locally constant sheaves are constant on the universal cover

Let `Y` be a scheme with universal profinite étale covers `p : Ỹ_y ⟶ Y`
(`AlgebraicGeometry.Scheme.UniversalCovers`), and `Λ` a finite ring. For a finite locally
constant sheaf `H` of `Λ`-modules on `Y_ét`:

- `AlgebraicGeometry.Scheme.UniversalCovers.bijective_sectionsGerm_upperStar`: the global
  sections of `p^* H` map bijectively to its stalk at the base point `ỹ`. Injectivity holds as
  `Ỹ_y` is connected; surjectivity by counting, the `Y`-morphisms `Ỹ_y ⟶ P` to the finite étale
  scheme `P` representing `H` (`AlgebraicGeometry.Scheme.FiniteEtale.toFLC`) giving as many
  sections of the base change `P ×_Y Ỹ_y`, hence of `p^* H`
  (`AlgebraicGeometry.Etale.isIso_upperStar_forget_comparison`,
  `AlgebraicGeometry.Scheme.FiniteEtale.toFLCPullbackIso`), as there are points of `P` over `y`
  (`AlgebraicGeometry.Scheme.UniversalCovers.bijective_fiber`).
- `AlgebraicGeometry.Scheme.UniversalCovers.upperStarIsoConstantSheaf`: hence
  `p^* H ≅ (H_y)_{Ỹ_y}` on `Ỹ_y,ét`, naturally in `H`;
- `AlgebraicGeometry.Scheme.UniversalCovers.comparisonUpperStarIsoConstantSheaf`: and
  `p^* ν^* H ≅ (H_y)_{Ỹ_y}` on `Ỹ_y,proét`, naturally in `H`, and for towers
  (`AlgebraicGeometry.Scheme.UniversalCovers.towerComparisonUpperStarIsoConstantSheaf`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

section Sections

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (U : Scheme.UniversalCovers Y Ω)
  (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
  {H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hH : IsFiniteLocallyConstantSheaf H)

instance UniversalCovers.instConnectedSpaceCover : ConnectedSpace (U.cover y) :=
  U.connectedSpace y

/-- The stalk of the pullback of a finite locally constant sheaf to the universal cover, at its
base point, has the cardinality of the geometric fibre of the representing finite étale
scheme. -/
lemma UniversalCovers.natCard_sheafFiber_upperStar (P : Y.FiniteEtale)
    (ι : (FiniteEtale.toFLC Y).obj P ≅ hH.toFLC) :
    Nat.card ((pointSmallEtale (U.pt y)).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y)).obj H)) =
      Nat.card ((FiniteEtale.fiber y).obj P) := by
  have c1 := Nat.card_congr ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ)
    (U.proj y) (U.pt y)).app H).toLinearEquiv.toEquiv
  refine c1.trans ?_
  have e : U.pt y ≫ U.proj y = y := U.pt_proj y
  rw [e]
  refine (Nat.card_congr (hH.stalkEquiv y)).trans ?_
  refine (Nat.card_congr ((pointSmallEtale y).sheafFiber.mapIso
      ((ObjectProperty.ι _).mapIso ι.symm)).toEquiv).trans ?_
  refine (Nat.card_congr ((FiniteEtale.toFLCCompSheafFiberIso y).app P).toEquiv).trans ?_
  exact Nat.card_ulift _

/-- The global sections of the pullback of a finite locally constant sheaf to the universal
cover are at least as many as the `Y`-morphisms `Ỹ_y ⟶ P` to the representing finite étale
scheme: each gives a section of `P ×_Y Ỹ_y`. -/
lemma UniversalCovers.natCard_le_sections_upperStar (P : Y.FiniteEtale)
    (ι : (FiniteEtale.toFLC Y).obj P ≅ hH.toFLC)
    [Finite (((Etale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y)).obj H).obj.obj
      (op (Etale.mk (𝟙 (U.cover y)))))] :
    Nat.card {f : U.cover y ⟶ P.obj.left // f ≫ P.obj.hom = U.proj y} ≤
      Nat.card (((Etale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y)).obj H).obj.obj
        (op (Etale.mk (𝟙 (U.cover y))))) := by
  let p := U.proj y
  have hκ := Etale.isIso_upperStar_forget_comparison Λ p H
  let κ := asIso (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ p) (Type (u + 1))
      (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
      ((U.cover y).smallGrothendieckTopology (Q := @Etale) @Etale)).homEquiv
      ((sheafCompose Y.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj H)
      ((sheafCompose (U.cover y).smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) p).obj H))).symm
        ((sheafCompose Y.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app H)))
  let θ : ((FiniteEtale.toFLC (U.cover y)).obj ((FiniteEtale.pullback p).obj P)).obj ≅
      (sheafCompose (U.cover y).smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) p).obj H) :=
    ((FiniteEtale.toFLCPullbackIso p).app P).symm ≪≫
      (etaleSetPullback p).mapIso ((ObjectProperty.ι _).mapIso ι) ≪≫ κ
  let T := Etale.mk (𝟙 (U.cover y))
  let g : {f : U.cover y ⟶ P.obj.left // f ≫ P.obj.hom = U.proj y} →
      ((FiniteEtale.toFLC (U.cover y)).obj ((FiniteEtale.pullback p).obj P)).obj.obj.obj (op T) :=
    fun a ↦ ULift.up (MorphismProperty.Over.homMk (pullback.lift a.1 (𝟙 _) (by simp [a.2, p]))
      (by simp [T, FiniteEtale.pullback]; rfl) trivial)
  have hg : Function.Injective g := by
    intro a b hab
    have := congrArg (fun z ↦ z.down.left ≫ pullback.fst _ _) hab
    erw [pullback.lift_fst, pullback.lift_fst] at this
    exact Subtype.ext this
  exact Nat.card_le_card_of_injective _
    ((((sheafToPresheaf _ _).mapIso θ).app (op T)).toEquiv.injective.comp hg)

include hH in
/-- **On the universal cover, the global sections of the pullback of a finite locally constant
sheaf map bijectively to its stalk at the base point**: injectively since the cover is
connected, and surjectively by counting, the sections including those coming from the
`Y`-morphisms `Ỹ_y ⟶ P` to the finite étale scheme `P` representing the sheaf, which are as many
as the points of its fibre at `y`. -/
theorem UniversalCovers.bijective_sectionsGerm_upperStar :
    Function.Bijective (sectionsGerm (U.pt y)
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y)).obj H)) := by
  have := hH
  have hG : IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y)).obj H) :=
    IsFiniteLocallyConstantSheaf.upperStar _ _
  have hinj := IsFiniteLocallyConstantSheaf.sectionsGerm_injective (U.pt y) hG
  have : Finite ((pointSmallEtale (U.pt y)).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y)).obj H)) := by
    have := (ModuleCat.isFinitelyGenerated_iff _).1
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
        (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
        (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y)).obj H) _ (U.pt y))
    exact Module.finite_of_finite Λ
  have : Finite (((Etale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y)).obj H).obj.obj
      (op (Etale.mk (𝟙 (U.cover y))))) := Finite.of_injective _ hinj
  let P := (FiniteEtale.toFLC Y).objPreimage hH.toFLC
  let ι : (FiniteEtale.toFLC Y).obj P ≅ hH.toFLC := (FiniteEtale.toFLC Y).objObjPreimageIso _
  refine hinj.bijective_of_nat_card_le ?_
  rw [U.natCard_sheafFiber_upperStar y hH P ι,
    ← Nat.card_congr (Equiv.ofBijective _ (U.bijective_fiber y P))]
  exact U.natCard_le_sections_upperStar y hH P ι

end Sections

section Constant

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (U : Scheme.UniversalCovers Y Ω)
  (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **Finite locally constant sheaves become constant on the universal cover**, naturally:
for a finite locally constant sheaf `H` of `Λ`-modules on `Y` (`Λ` finite), the pullback of `H`
to the universal profinite étale cover `Ỹ_y` is the constant sheaf with value the stalk `H_y`.
The counit `Γ(Ỹ_y, p^* H)_{Ỹ_y} ⟶ p^* H` and the germ `Γ(Ỹ_y, p^* H) ⟶ (p^* H)_ỹ ≅ H_y` are
isomorphisms (`AlgebraicGeometry.Scheme.UniversalCovers.bijective_sectionsGerm_upperStar`). -/
noncomputable def UniversalCovers.upperStarIsoConstantSheaf :
    ObjectProperty.ι (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
        IsFiniteLocallyConstantSheaf F) ⋙ Etale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y) ≅
      ObjectProperty.ι _ ⋙ (pointSmallEtale (U.pt y ≫ U.proj y)).sheafFiber ⋙
        constantSheaf (U.cover y).smallEtaleTopology (ModuleCat.{u + 1} Λ) := by
  let T := Etale.mk (𝟙 (U.cover y))
  let adj := constantSheafAdj (U.cover y).smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (Etale.isTerminalMkId (U.cover y))
  let K := ObjectProperty.ι (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
    IsFiniteLocallyConstantSheaf F) ⋙ Etale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y)
  let germ : (sheafSections (U.cover y).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op T) ⟶
      (pointSmallEtale (U.pt y)).sheafFiber :=
    Functor.whiskerLeft (sheafToPresheaf _ _)
      ((pointSmallEtale (U.pt y)).toPresheafFiberNatTrans T (Over.homMk (U.pt y)))
  let α : K ⋙ (sheafSections (U.cover y).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op T) ⋙
      constantSheaf (U.cover y).smallEtaleTopology (ModuleCat.{u + 1} Λ) ⟶ K :=
    Functor.whiskerLeft K adj.counit ≫ (Functor.rightUnitor K).hom
  let β : K ⋙ (sheafSections (U.cover y).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op T) ⋙
      constantSheaf (U.cover y).smallEtaleTopology (ModuleCat.{u + 1} Λ) ⟶
      K ⋙ (pointSmallEtale (U.pt y)).sheafFiber ⋙
        constantSheaf (U.cover y).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    Functor.whiskerLeft K (Functor.whiskerRight germ _)
  have hb (F : ObjectProperty.FullSubcategory
      (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
        IsFiniteLocallyConstantSheaf F)) :=
    U.bijective_sectionsGerm_upperStar y F.property
  have : ∀ F, IsIso (α.app F) := fun F ↦ by
    have := F.property
    have h2 : IsFiniteLocallyConstantSheaf (K.obj F) :=
      IsFiniteLocallyConstantSheaf.upperStar (U.proj y) F.obj
    have h : IsIso (adj.counit.app (K.obj F)) :=
      IsFiniteLocallyConstantSheaf.isIso_constantSheafAdj_counit (U.pt y) h2 (hb F)
    change IsIso (adj.counit.app (K.obj F) ≫ 𝟙 _)
    infer_instance
  have : ∀ F, IsIso (β.app F) := fun F ↦ by
    have : IsIso (sectionsGerm (U.pt y) (K.obj F)) :=
      (ConcreteCategory.isIso_iff_bijective _).2 (hb F)
    change IsIso ((constantSheaf (U.cover y).smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
      (sectionsGerm (U.pt y) (K.obj F)))
    infer_instance
  have := NatIso.isIso_of_isIso_app α
  have := NatIso.isIso_of_isIso_app β
  exact (asIso α).symm ≪≫ asIso β ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι _) (Functor.isoWhiskerRight
      (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) (U.proj y) (U.pt y)) _)

/-- **The comparison pullback of a finite locally constant sheaf is constant on the universal
cover**, naturally: `p^* ν^* H ≅ (H_y)_{Ỹ_y}` on the pro-étale site of `Ỹ_y`. -/
noncomputable def UniversalCovers.comparisonUpperStarIsoConstantSheaf :
    ObjectProperty.ι (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
        IsFiniteLocallyConstantSheaf F) ⋙ ProEtale.comparisonUpperStar _ Y ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y) ≅
      ObjectProperty.ι _ ⋙ (pointSmallEtale (U.pt y ≫ U.proj y)).sheafFiber ⋙
        constantSheaf (ProEt.topology (U.cover y)) (ModuleCat.{u + 1} Λ) :=
  Functor.isoWhiskerLeft _ (ProEtale.comparisonUpperStarCompUpperStarIso _ (U.proj y)) ≪≫
    Functor.isoWhiskerRight (U.upperStarIsoConstantSheaf y Λ)
      (ProEtale.comparisonUpperStar _ (U.cover y)) ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι _ ⋙ (pointSmallEtale (U.pt y ≫ U.proj y)).sheafFiber)
      (ProEtale.constantSheafCompComparisonUpperStarIso _ (U.cover y))

/-- **A tower of finite locally constant sheaves becomes a tower of constant sheaves on the
universal cover**: `p^* ν^* Hₙ ≅ ((Hₙ)_y)_{Ỹ_y}`, compatibly with the transitions, whose values
form the tower of stalks at `y`. -/
noncomputable def UniversalCovers.towerComparisonUpperStarIsoConstantSheaf
    (H : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hH : ∀ n : ℕ, IsFiniteLocallyConstantSheaf (H.obj (op n))) :
    H ⋙ ProEtale.comparisonUpperStar _ Y ⋙ ProEtale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y) ≅
      H ⋙ (pointSmallEtale (U.pt y ≫ U.proj y)).sheafFiber ⋙
        constantSheaf (ProEt.topology (U.cover y)) (ModuleCat.{u + 1} Λ) :=
  Functor.isoWhiskerLeft (ObjectProperty.lift _ H fun n ↦ hH n.unop)
    (U.comparisonUpperStarIsoConstantSheaf y Λ)

end Constant

end AlgebraicGeometry.Scheme
