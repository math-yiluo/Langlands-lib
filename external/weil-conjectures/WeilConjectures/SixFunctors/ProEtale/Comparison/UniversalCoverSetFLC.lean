/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.SetLocallyConstant
public import WeilConjectures.SixFunctors.ProEtale.Adic.UniversalCoverTowerLimit
public import Mathlib.Algebra.Group.Shrink

/-!
# Locally constant sheaves with finite stalks on the universal cover, for any coefficients

The results of `WeilConjectures.SixFunctors.ProEtale.Comparison.UniversalCoverConstant` for
sheaves of `Λ`-modules over an arbitrary ring `Λ` whose underlying sheaves of sets are finite
locally constant (`AlgebraicGeometry.Scheme.IsSetFLC`), e.g. abelian sheaves with finite stalks
via `Λ = ULift ℤ`:

- `AlgebraicGeometry.Scheme.IsSetFLC.upperStar`: stability under pullback;
- `AlgebraicGeometry.Scheme.UniversalCovers.bijective_sectionsGerm'_upperStar`,
  `UniversalCovers.upperStarIsoConstantSheaf'`,
  `UniversalCovers.comparisonUpperStarIsoConstantSheaf'`,
  `UniversalCovers.towerComparisonUpperStarIsoConstantSheaf'`: such sheaves (and towers of them)
  become constant with value the stalk at `y` on the universal cover `Ỹ_y`, naturally;
- `AlgebraicGeometry.Scheme.UniversalCovers.exists_isLimit_towerComparisonUpperStar'`: the
  abelian tower underlying `p^* ν^* Hₙ` has limit `C(-, lim_n (Hₙ)_y)`, the finite stalks being
  made discrete groups in `Type` (`DiscreteShrink`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

section Pullback

variable {X Z : Scheme.{u}} (g : Z ⟶ X) {Λ : Type (u + 1)} [Ring Λ]
  {H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hH : IsSetFLC H) (P : X.FiniteEtale)
  (ι : (FiniteEtale.toFLC X).obj P ≅ hH.toFLC)

/-- The underlying sheaf of sets of the pullback of a sheaf of modules represented by a finite
étale `P` is represented by the base change of `P`. -/
noncomputable def IsSetFLC.forgetUpperStarIso :
    ((FiniteEtale.toFLC Z).obj ((FiniteEtale.pullback g).obj P)).obj ≅
      (sheafCompose Z.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj H) :=
  have := Etale.isIso_upperStar_forget_comparison Λ g H
  ((FiniteEtale.toFLCPullbackIso g).app P).symm ≪≫
    (etaleSetPullback g).mapIso ((ObjectProperty.ι _).mapIso ι) ≪≫
    asIso (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
      (X.smallGrothendieckTopology (Q := @Etale) @Etale)
      (Z.smallGrothendieckTopology (Q := @Etale) @Etale)).homEquiv
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj H)
      ((sheafCompose Z.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj H))).symm
        ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app H)))

include hH in
/-- Pullback preserves sheaves of modules with finite locally constant underlying sheaf of
sets. -/
lemma IsSetFLC.upperStar : IsSetFLC ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj H) :=
  IsFiniteLocallyConstantSheafOfTypes.of_iso
    (hH.forgetUpperStarIso g _ ((FiniteEtale.toFLC X).objObjPreimageIso _))
    ((FiniteEtale.toFLC Z).obj _).property

end Pullback

section Sections

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (U : Scheme.UniversalCovers Y Ω)
  (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {Λ : Type (u + 1)} [Ring Λ]
  {H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hH : IsSetFLC H)

/-- The stalk of the pullback to the universal cover has the cardinality of the geometric fibre of
the representing finite étale scheme. -/
lemma UniversalCovers.natCard_sheafFiber_upperStar' (P : Y.FiniteEtale)
    (ι : (FiniteEtale.toFLC Y).obj P ≅ hH.toFLC) :
    Nat.card ((pointSmallEtale (U.pt y)).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y)).obj H)) =
      Nat.card ((FiniteEtale.fiber y).obj P) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have c1 := Nat.card_congr ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ)
    (U.proj y) (U.pt y)).app H).toLinearEquiv.toEquiv
  refine c1.trans ?_
  have e : U.pt y ≫ U.proj y = y := U.pt_proj y
  rw [e]
  refine (Nat.card_congr (((pointSmallEtale y).sheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app H).toEquiv.symm).trans ?_
  refine (Nat.card_congr ((pointSmallEtale y).sheafFiber.mapIso
      ((ObjectProperty.ι _).mapIso ι.symm)).toEquiv).trans ?_
  refine (Nat.card_congr ((FiniteEtale.toFLCCompSheafFiberIso y).app P).toEquiv).trans ?_
  exact Nat.card_ulift _

/-- The global sections of the pullback to the universal cover are at least as many as the
`Y`-morphisms `Ỹ_y ⟶ P`. -/
lemma UniversalCovers.natCard_le_sections_upperStar' (P : Y.FiniteEtale)
    (ι : (FiniteEtale.toFLC Y).obj P ≅ hH.toFLC)
    [Finite (((Etale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y)).obj H).obj.obj
      (op (Etale.mk (𝟙 (U.cover y)))))] :
    Nat.card {f : U.cover y ⟶ P.obj.left // f ≫ P.obj.hom = U.proj y} ≤
      Nat.card (((Etale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y)).obj H).obj.obj
        (op (Etale.mk (𝟙 (U.cover y))))) := by
  let p := U.proj y
  let θ := hH.forgetUpperStarIso p P ι
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
/-- **On the universal cover, global sections of the pullback of a sheaf of modules with finite
locally constant underlying sheaf of sets map bijectively to the stalk at the base point.** -/
theorem UniversalCovers.bijective_sectionsGerm'_upperStar :
    Function.Bijective (sectionsGerm' (U.pt y)
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y)).obj H)) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have hG := hH.upperStar (U.proj y)
  have hinj := IsSetFLC.sectionsGerm'_injective (U.pt y) hG
  have : Finite ((pointSmallEtale (U.pt y)).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y)).obj H)) := by
    have := (ConcreteCategory.isFinitelyGenerated_iff_finite _).1
      (hG.2.isFinitelyGenerated_sheafFiber _ (U.pt y))
    exact Finite.of_equiv _ (((pointSmallEtale (U.pt y)).sheafFiberCompIso
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app _).toEquiv
  have : Finite (((Etale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y)).obj H).obj.obj
      (op (Etale.mk (𝟙 (U.cover y))))) := Finite.of_injective _ hinj
  let P := (FiniteEtale.toFLC Y).objPreimage hH.toFLC
  let ι : (FiniteEtale.toFLC Y).obj P ≅ hH.toFLC := (FiniteEtale.toFLC Y).objObjPreimageIso _
  refine hinj.bijective_of_nat_card_le ?_
  rw [U.natCard_sheafFiber_upperStar' y hH P ι,
    ← Nat.card_congr (Equiv.ofBijective _ (U.bijective_fiber y P))]
  exact U.natCard_le_sections_upperStar' y hH P ι

end Sections

section Constant

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (U : Scheme.UniversalCovers Y Ω)
  (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (Λ : Type (u + 1)) [Ring Λ]

/-- **Finite locally constant sheaves become constant on the universal cover**, naturally:
for a sheaf `H` of `Λ`-modules on `Y` with finite locally constant underlying sheaf of sets, the
pullback of `H`
to the universal profinite étale cover `Ỹ_y` is the constant sheaf with value the stalk `H_y`.
The counit `Γ(Ỹ_y, p^* H)_{Ỹ_y} ⟶ p^* H` and the germ `Γ(Ỹ_y, p^* H) ⟶ (p^* H)_ỹ ≅ H_y` are
isomorphisms (`AlgebraicGeometry.Scheme.UniversalCovers.bijective_sectionsGerm_upperStar`). -/
noncomputable def UniversalCovers.upperStarIsoConstantSheaf' :
    ObjectProperty.ι (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
        IsSetFLC F) ⋙ Etale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y) ≅
      ObjectProperty.ι _ ⋙ (pointSmallEtale (U.pt y ≫ U.proj y)).sheafFiber ⋙
        constantSheaf (U.cover y).smallEtaleTopology (ModuleCat.{u + 1} Λ) := by
  let T := Etale.mk (𝟙 (U.cover y))
  let adj := constantSheafAdj (U.cover y).smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (Etale.isTerminalMkId (U.cover y))
  let K := ObjectProperty.ι (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
    IsSetFLC F) ⋙ Etale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y)
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
        IsSetFLC F)) :=
    U.bijective_sectionsGerm'_upperStar y F.property
  have : ∀ F, IsIso (α.app F) := fun F ↦ by
    have h2 : IsSetFLC (K.obj F) := F.property.upperStar (U.proj y)
    have h : IsIso (adj.counit.app (K.obj F)) :=
      IsSetFLC.isIso_constantSheafAdj_counit (U.pt y) h2 (hb F)
    change IsIso (adj.counit.app (K.obj F) ≫ 𝟙 _)
    infer_instance
  have : ∀ F, IsIso (β.app F) := fun F ↦ by
    have : IsIso (sectionsGerm' (U.pt y) (K.obj F)) :=
      (ConcreteCategory.isIso_iff_bijective _).2 (hb F)
    change IsIso ((constantSheaf (U.cover y).smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
      (sectionsGerm' (U.pt y) (K.obj F)))
    infer_instance
  have := NatIso.isIso_of_isIso_app α
  have := NatIso.isIso_of_isIso_app β
  exact (asIso α).symm ≪≫ asIso β ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι _) (Functor.isoWhiskerRight
      (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) (U.proj y) (U.pt y)) _)

/-- **The comparison pullback of a finite locally constant sheaf is constant on the universal
cover**, naturally: `p^* ν^* H ≅ (H_y)_{Ỹ_y}` on the pro-étale site of `Ỹ_y`. -/
noncomputable def UniversalCovers.comparisonUpperStarIsoConstantSheaf' :
    ObjectProperty.ι (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
        IsSetFLC F) ⋙ ProEtale.comparisonUpperStar _ Y ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y) ≅
      ObjectProperty.ι _ ⋙ (pointSmallEtale (U.pt y ≫ U.proj y)).sheafFiber ⋙
        constantSheaf (ProEt.topology (U.cover y)) (ModuleCat.{u + 1} Λ) :=
  Functor.isoWhiskerLeft _ (ProEtale.comparisonUpperStarCompUpperStarIso _ (U.proj y)) ≪≫
    Functor.isoWhiskerRight (U.upperStarIsoConstantSheaf' y Λ)
      (ProEtale.comparisonUpperStar _ (U.cover y)) ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι _ ⋙ (pointSmallEtale (U.pt y ≫ U.proj y)).sheafFiber)
      (ProEtale.constantSheafCompComparisonUpperStarIso _ (U.cover y))

/-- **A tower of finite locally constant sheaves becomes a tower of constant sheaves on the
universal cover**: `p^* ν^* Hₙ ≅ ((Hₙ)_y)_{Ỹ_y}`, compatibly with the transitions, whose values
form the tower of stalks at `y`. -/
noncomputable def UniversalCovers.towerComparisonUpperStarIsoConstantSheaf'
    (H : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hH : ∀ n : ℕ, IsSetFLC (H.obj (op n))) :
    H ⋙ ProEtale.comparisonUpperStar _ Y ⋙ ProEtale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y) ≅
      H ⋙ (pointSmallEtale (U.pt y ≫ U.proj y)).sheafFiber ⋙
        constantSheaf (ProEt.topology (U.cover y)) (ModuleCat.{u + 1} Λ) :=
  Functor.isoWhiskerLeft (ObjectProperty.lift _ H fun n ↦ hH n.unop)
    (U.comparisonUpperStarIsoConstantSheaf' y Λ)

end Constant


end AlgebraicGeometry.Scheme

/-- A finite type, shrunk to `Type` and given the discrete topology (with the transported additive
structure when it has one). -/
def DiscreteShrink (α : Type*) [Small.{0} α] : Type := Shrink.{0} α

namespace DiscreteShrink

variable (α : Type*) [Small.{0} α]

noncomputable instance [AddCommGroup α] : AddCommGroup (DiscreteShrink α) :=
  inferInstanceAs (AddCommGroup (Shrink.{0} α))

instance : TopologicalSpace (DiscreteShrink α) := ⊥

instance : DiscreteTopology (DiscreteShrink α) := ⟨rfl⟩

instance [AddCommGroup α] : IsTopologicalAddGroup (DiscreteShrink α) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

/-- The additive equivalence with the shrunk type. -/
noncomputable def addEquiv [AddCommGroup α] : α ≃+ DiscreteShrink α where
  toEquiv := equivShrink α
  map_add' := equivShrink_add

/-- An additive map, transported to the shrunk types. -/
noncomputable def map {α β : Type*} [Small.{0} α] [Small.{0} β] [AddCommGroup α] [AddCommGroup β]
    (f : α →+ β) : DiscreteShrink α →+ DiscreteShrink β :=
  (addEquiv β).toAddMonoidHom.comp (f.comp (addEquiv α).symm.toAddMonoidHom)

end DiscreteShrink

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (U : Scheme.UniversalCovers Y Ω)
  (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {Λ : Type (u + 1)} [Ring Λ]

/-- The stalk at a geometric point of a sheaf of modules with finite locally constant underlying
sheaf of sets is finite. -/
lemma IsSetFLC.finite_sheafFiber {X : Scheme.{u}}
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hF : IsSetFLC F) {K : Type u} [Field K] [IsSepClosed K] (t : Spec (.of K) ⟶ X) :
    Finite ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj F) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have := (ConcreteCategory.isFinitelyGenerated_iff_finite _).1
    (hF.2.isFinitelyGenerated_sheafFiber K t)
  exact Finite.of_equiv _ (((pointSmallEtale t).sheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app F).toEquiv

/-- **The limit of a tower of locally constant sheaves with finite stalks on the universal
cover.** For a tower `H` of étale sheaves of `Λ`-modules on `Y` (any ring `Λ`, e.g.
`ULift 𝒪_E` or `ULift ℤ`) whose underlying sheaves of sets are finite locally constant, the
abelian tower underlying `p^* ν^* Hₙ` on the universal cover `Ỹ_y` has limit
`C(-, lim_n (Hₙ)_y)`, the stalks being made discrete groups in `Type`. -/
theorem UniversalCovers.exists_isLimit_towerComparisonUpperStar'
    (H : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hH : ∀ n : ℕ, IsSetFLC (H.obj (op n))) :
    let St := (pointSmallEtale (U.pt y ≫ U.proj y)).sheafFiber (A := ModuleCat.{u + 1} Λ)
    have (n : ℕ) : Finite (St.obj (H.obj (op n))) := (hH n).finite_sheafFiber _
    ∃ c : Cone (H ⋙ ProEtale.comparisonUpperStar _ Y ⋙ ProEtale.upperStar _ (U.proj y) ⋙
        sheafCompose (ProEt.topology (U.cover y))
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})),
      c.pt = ProEtale.continuousMapAddSheaf (U.cover y)
        (ProEtale.towerLimitAddSubgroup (Qs := fun n ↦ DiscreteShrink (St.obj (H.obj (op n))))
          (fun n ↦ DiscreteShrink.map
          (St.map (H.map (homOfLE (n.le_add_right 1)).op)).hom.toAddMonoidHom)) ∧
        Nonempty (IsLimit c) := by
  intro St hfin
  refine ProEtale.exists_isLimit_continuousMapAddSheaf_of_iso (U.cover y) _
    (H ⋙ St) (fun n ↦ (DiscreteShrink.addEquiv (St.obj (H.obj (op n)))).trans
      AddEquiv.ulift.symm) (fun n x ↦ ?_)
    (Functor.isoWhiskerRight (U.towerComparisonUpperStarIsoConstantSheaf' y Λ H hH)
      (sheafCompose (ProEt.topology (U.cover y))
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
  change ULift.up _ = ULift.up _
  simp only [DiscreteShrink.map, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  have hx : (((DiscreteShrink.addEquiv (St.obj (H.obj (op (n + 1))))).trans
      (AddEquiv.ulift.{0, u + 1}).symm) x).down =
        DiscreteShrink.addEquiv (St.obj (H.obj (op (n + 1)))) x :=
    rfl
  erw [hx, AddEquiv.symm_apply_apply]
  rfl

end AlgebraicGeometry.Scheme
