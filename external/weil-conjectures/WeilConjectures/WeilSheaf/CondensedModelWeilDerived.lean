/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
public import WeilConjectures.WeilSheaf.CondensedModelWeil
public import WeilConjectures.WeilSheaf.ExtensionByZeroAdjunction
public import WeilConjectures.WeilSheaf.LowerShriek

/-!
# Weil complexes in the condensed model

Let `k₀` be a finite field and `X` a `k₀`-scheme with geometric fibre `X̄` and geometric Galois
Frobenius `Fr_X`. The equivalence `E = AlgebraicGeometry.ProEtaleWeilSheaf.toCondensed` identifies
the pro-étale Weil sheaves of the old model, `ℓ`-adic sheaves `F` on `X̄` with `(Fr_X⁻¹)_* F ≅ F`,
with condensed Weil objects: module objects `M` over `Λ = ℚ̲̄_ℓ` on `X̄` with
`(Fr_X⁻¹)_* M ≅ M`. Being an exact equivalence of abelian categories, it induces an equivalence of
derived categories `D(E)`. We show that `E` and `D(E)` intertwine the Weil functors of the two
models:

- pushforward `φ_*`: the comparison `AlgebraicGeometry.ProEtale.adicLowerStarCompCondensedModIso`
  along the base change `φ̄` is compatible with the Frobenius exchange isomorphisms of the two
  models (`AlgebraicGeometry.ProEtale.exchangeCompatible_lowerStar_geometricFiberMap`), so it
  lifts to Weil objects (`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoCompIsoOfExchange`);
- pullback `φ^*` and extension by zero `j_!`: in the new model their Weil structures are defined
  as mates (`CategoryTheory.Endofunctor.IsoAlgebra.leftMateIso`), so that the adjunctions
  `j_! ⊣ j^* ⊣ j_*` lift to condensed Weil objects; the compatibilities are then the conjugates
  (`CategoryTheory.Adjunction.leftAdjointCompIsoOfEquivalence`) of that of the pushforward;
- the derived functors `Rφ_*`, `D(φ^*)`, `D(j_!)` and the direct image with compact support
  `Rf_! = Rḡ_* ∘ D(ī_!)` attached to a compactification, hence
  `AlgebraicGeometry.WeilComplex.derivedLowerShriek`.

## Main results

- `AlgebraicGeometry.ProEtaleWeilSheaf.derivedEquivCondensed`: the derived equivalence.
- `AlgebraicGeometry.ProEtaleWeilSheaf.lowerStarCompToCondensedIso`,
  `AlgebraicGeometry.ProEtaleWeilSheaf.upperStarCompToCondensedIso` and
  `AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZeroCompToCondensedIso`: the Weil functors.
- `AlgebraicGeometry.ProEtaleWeilSheaf.rightDerivedLowerStarCompToCondensedIso`:
  `Rφ_* ⋙ D(E) ≅ D(E) ⋙ Rφ_*`.
- `AlgebraicGeometry.ProEtaleWeilSheaf.rightDerivedLowerShriekCompIso`:
  `Rf_! ⋙ D(E) ≅ D(E) ⋙ Rf_!` for a compactification.
- `AlgebraicGeometry.WeilComplex.derivedLowerShriekCompToCondensedIso`: the same for
  `AlgebraicGeometry.WeilComplex.derivedLowerShriek`.

## Implementation notes

The coherence `AlgebraicGeometry.ProEtale.exchangeCompatible_adicLowerStarCompCondensedModIso` is
stated through the predicate `CategoryTheory.Endofunctor.IsoAlgebra.ExchangeCompatible`, so that
its instance along the geometric fibres is checked by the kernel by unfolding the exchange
isomorphisms only, not the module objects.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

/-! ### Abstract preliminaries -/

namespace CategoryTheory

section Mates

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}

/-- The mate of an isomorphism along adjunctions whose units and counits are isomorphisms (for
instance, along equivalences) is an isomorphism. -/
lemma isIso_mateEquiv_natTrans (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [IsIso adj₁.counit]
    [IsIso adj₂.unit] (α : TwoSquare G L₁ L₂ H) [IsIso α] :
    IsIso (mateEquiv adj₁ adj₂ α) := by
  have (d : B) : IsIso ((mateEquiv adj₁ adj₂ α).app d) := by
    simp only [mateEquiv_apply, NatTrans.comp_app]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end Mates

namespace Endofunctor.IsoAlgebra

section LeftMate

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D}
  {R : D ⥤ C} (adj : L ⊣ R) (eR : R ⋙ F ≅ G ⋙ R) [F.IsEquivalence] [G.IsEquivalence]

/-- If `F` and `G` are equivalences, the mate `F ⋙ L ⟶ L ⋙ G` of an isomorphism
`eR : R ⋙ F ≅ G ⋙ R` along `L ⊣ R` is an isomorphism: its mate along the adjunctions `F ⊣ F⁻¹`
and `G ⊣ G⁻¹` is the conjugate of the mate of `eR`
(`CategoryTheory.iterated_mateEquiv_conjugateEquiv`), which is an isomorphism. -/
instance isIso_mateEquiv_symm :
    IsIso ((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ eR.hom)) := by
  have : IsIso G.asEquivalence.toAdjunction.counit :=
    inferInstanceAs (IsIso G.asEquivalence.counitIso.hom)
  have : IsIso F.asEquivalence.toAdjunction.unit :=
    inferInstanceAs (IsIso F.asEquivalence.unitIso.hom)
  have h := iterated_mateEquiv_conjugateEquiv adj adj F.asEquivalence.toAdjunction
    G.asEquivalence.toAdjunction ((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ eR.hom))
  rw [Equiv.apply_symm_apply] at h
  have : IsIso (mateEquiv G.asEquivalence.toAdjunction F.asEquivalence.toAdjunction
      (TwoSquare.mk _ _ _ _ eR.hom)) :=
    isIso_mateEquiv_natTrans _ _ (TwoSquare.mk _ _ _ _ eR.hom)
  rw [h] at this
  exact conjugateEquiv_of_iso (adj.comp G.asEquivalence.toAdjunction)
    (F.asEquivalence.toAdjunction.comp adj) _

/-- If `F` and `G` are equivalences, an isomorphism `eR : R ⋙ F ≅ G ⋙ R` for the right adjoint
`R` of `L` gives the isomorphism `L ⋙ G ≅ F ⋙ L` whose inverse is the mate of `eR`; then
`L ⊣ R` lifts to algebras (`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction` and
`CategoryTheory.Endofunctor.IsoAlgebra.mateEquiv_leftMateIso_inv`). -/
noncomputable def leftMateIso : L ⋙ G ≅ F ⋙ L :=
  (asIso ((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ eR.hom))).symm

/-- The mate of the inverse of `CategoryTheory.Endofunctor.IsoAlgebra.leftMateIso adj eR` is
`eR`. -/
lemma mateEquiv_leftMateIso_inv :
    (mateEquiv adj adj (TwoSquare.mk _ _ _ _ (leftMateIso adj eR).inv)) = eR.hom := by
  rw [leftMateIso, Iso.symm_inv, asIso_hom]
  exact ((mateEquiv adj adj).apply_symm_apply _)

end LeftMate

section Exchange

variable {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
  {F : C ⥤ C} {F' : C' ⥤ C'} {G : D ⥤ D} {G' : D' ⥤ D'} {E : C ⥤ D} {E' : C' ⥤ D'}
  {P : C ⥤ C'} {Q : D ⥤ D'}

/-- The compatibility of an isomorphism `γ : P ⋙ E' ≅ E ⋙ Q` with exchange isomorphisms
`α : P ⋙ F' ≅ F ⋙ P`, `β : Q ⋙ G' ≅ G ⋙ Q`, `ε : F ⋙ E ≅ E ⋙ G` and `ε' : F' ⋙ E' ≅ E' ⋙ G'`:
the two ways of going from `E' F' P` to `Q G E` around the cube agree. -/
def ExchangeCompatible (α : P ⋙ F' ≅ F ⋙ P) (ε : F ⋙ E ≅ E ⋙ G) (ε' : F' ⋙ E' ≅ E' ⋙ G')
    (β : Q ⋙ G' ≅ G ⋙ Q) (γ : P ⋙ E' ≅ E ⋙ Q) : Prop :=
  ∀ K, ε'.hom.app (P.obj K) ≫ G'.map (γ.hom.app K) ≫ β.hom.app (E.obj K) =
    E'.map (α.hom.app K) ≫ γ.hom.app (F.obj K) ≫ Q.map (ε.hom.app K)

/-- **Transport of algebras along a commutative square.** Let `E : C ⥤ D` and `E' : C' ⥤ D'`
carry endofunctors `F, G` and `F', G'` up to `ε : F ⋙ E ≅ E ⋙ G` and `ε'`, and let
`P : C ⥤ C'`, `Q : D ⥤ D'` commute with them up to `α : P ⋙ F' ≅ F ⋙ P` and
`β : Q ⋙ G' ≅ G ⋙ Q`. An isomorphism `γ : P ⋙ E' ≅ E ⋙ Q` compatible with these exchange
isomorphisms induces an isomorphism of the transported functors of algebras. -/
noncomputable def mapOfNatIsoCompIsoOfExchange {α : P ⋙ F' ≅ F ⋙ P} {ε : F ⋙ E ≅ E ⋙ G}
    {ε' : F' ⋙ E' ≅ E' ⋙ G'} {β : Q ⋙ G' ≅ G ⋙ Q} (γ : P ⋙ E' ≅ E ⋙ Q)
    (hγ : ExchangeCompatible α ε ε' β γ) :
    mapOfNatIso α ⋙ mapOfNatIso ε'.symm ≅ mapOfNatIso ε.symm ⋙ mapOfNatIso β :=
  mapOfNatIsoCompIso α ε'.symm ≪≫ mapOfNatIsoIsoOfIso γ (by
    ext K
    have h := hγ K
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      compCommIso_hom_app, Iso.symm_hom]
    rw [← cancel_epi (ε'.hom.app (P.obj K)), reassoc_of% h]
    simp [← Q.map_comp]) ≪≫
    (mapOfNatIsoCompIso ε.symm β).symm

end Exchange

end Endofunctor.IsoAlgebra

end CategoryTheory

/-! ### The exchange isomorphisms of the pushforwards across the two models -/

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

/-- The comparison `AdicSheaf ℓ S ≌ Mod_{Λ_S}` acts on underlying morphisms by forgetting the
`ℚ̄_ℓ`-module structure. -/
lemma adicSheafEquivCondensedMod_functor_map_hom {S : Scheme.{u}} {M N : AdicSheaf l S}
    (φ : M ⟶ N) : ((adicSheafEquivCondensedMod l S).functor.map φ).hom =
      (weilCoefficientsForgetAb l S).map φ.hom :=
  rfl

/-- The underlying sheaf of the module object attached to `M` is `forgetAb M`; the following three
lemmas record this for the components of the composition and congruence isomorphisms, in the form
used to guide the kernel in
`AlgebraicGeometry.ProEtale.exchangeCompatible_adicLowerStarCompCondensedModIso`. -/
lemma lowerStarComp_hom_app_adicSheafEquivCondensedMod_obj_X {S T T' : Scheme.{u}} (a : S ⟶ T)
    (b : T ⟶ T') (M : AdicSheaf l S) :
    (lowerStarComp Ab a b).hom.app ((weilCoefficientsForgetAb l S).obj M.X) =
      (lowerStarComp Ab a b).hom.app ((adicSheafEquivCondensedMod l S).functor.obj M).X :=
  rfl

lemma lowerStarComp_inv_app_adicSheafEquivCondensedMod_obj_X {S T T' : Scheme.{u}} (a : S ⟶ T)
    (b : T ⟶ T') (M : AdicSheaf l S) :
    (lowerStarComp Ab a b).inv.app ((weilCoefficientsForgetAb l S).obj M.X) =
      (lowerStarComp Ab a b).inv.app ((adicSheafEquivCondensedMod l S).functor.obj M).X :=
  rfl

lemma lowerStarCongr_hom_app_adicSheafEquivCondensedMod_obj_X {S T : Scheme.{u}} {a b : S ⟶ T}
    (h : a = b) (M : AdicSheaf l S) :
    (lowerStarCongr Ab h).hom.app ((weilCoefficientsForgetAb l S).obj M.X) =
      (lowerStarCongr Ab h).hom.app ((adicSheafEquivCondensedMod l S).functor.obj M).X :=
  rfl

/-- Forgetting the `ℚ̄_ℓ`-module structure of sheaves commutes with the composition isomorphisms
of the pushforwards. -/
lemma weilCoefficientsForgetAb_map_lowerStarComp_hom_app {R S T : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R) (G : Sheaf (Scheme.ProEt.topology T) (WeilCoefficients.{u} l)) :
    (weilCoefficientsForgetAb l R).map ((lowerStarComp (WeilCoefficients.{u} l) h₁ h₂).hom.app G) =
      (lowerStarComp Ab.{u + 1} h₁ h₂).hom.app ((weilCoefficientsForgetAb l T).obj G) :=
  rfl

lemma weilCoefficientsForgetAb_map_lowerStarComp_inv_app {R S T : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R) (G : Sheaf (Scheme.ProEt.topology T) (WeilCoefficients.{u} l)) :
    (weilCoefficientsForgetAb l R).map ((lowerStarComp (WeilCoefficients.{u} l) h₁ h₂).inv.app G) =
      (lowerStarComp Ab.{u + 1} h₁ h₂).inv.app ((weilCoefficientsForgetAb l T).obj G) :=
  rfl

/-- Forgetting the `ℚ̄_ℓ`-module structure of sheaves commutes with the congruence isomorphisms
of the pushforwards. -/
lemma weilCoefficientsForgetAb_map_lowerStarCongr_hom_app {S T : Scheme.{u}} {g g' : T ⟶ S}
    (h : g = g') (G : Sheaf (Scheme.ProEt.topology T) (WeilCoefficients.{u} l)) :
    (weilCoefficientsForgetAb l S).map ((lowerStarCongr (WeilCoefficients.{u} l) h).hom.app G) =
      (lowerStarCongr Ab.{u + 1} h).hom.app ((weilCoefficientsForgetAb l T).obj G) := by
  subst h
  rfl

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y Z : Scheme.{u}}

omit [IsCommMonObj Λ] in
/-- On underlying sheaves, the inverse of the composition isomorphism of the pushforwards of
module objects is that of the pushforwards of sheaves. -/
lemma lowerStarComp_inv_app_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((lowerStarComp Λ f g).inv.app M).hom =
      (ProEtale.lowerStarComp Ab.{u + 1} f g).inv.app M.X := by
  rw [← cancel_epi ((ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app M.X), Iso.hom_inv_id_app,
    ← lowerStarComp_hom_app_hom, ← Mod.comp_hom', Iso.hom_inv_id_app]
  rfl

/-- The pushforward of module objects over `Λ` along an isomorphism is an equivalence. -/
instance isEquivalence_lowerStar (f : X ⟶ Y) [IsIso f] : (lowerStar Λ f).IsEquivalence :=
  (lowerStarEquivalenceOfIso Λ (asIso f)).isEquivalence_functor

/-- Module objects over `Λ` with an isomorphism `e_* M ≅ M`, for an automorphism `e`, form a
Grothendieck abelian category. -/
instance isGrothendieckAbelian_isoAlgebra_lowerStar (e : X ⟶ X) [IsIso e] :
    IsGrothendieckAbelian.{u + 1} (Endofunctor.IsoAlgebra (lowerStar Λ e)) :=
  Endofunctor.IsoAlgebra.isGrothendieckAbelian _

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

/-- **The pushforward compatibility of the two models is compatible with the exchange
isomorphisms**: for `a ≫ b = c ≫ a`, the comparisons
`AlgebraicGeometry.ProEtale.adicLowerStarCompCondensedModIso` intertwine the exchange isomorphism
`a_* ⋙ b_* ≅ (a ≫ b)_* = (c ≫ a)_* ≅ c_* ⋙ a_*` of `ℓ`-adic sheaves with that of module objects
over `Λ`. All the comparisons have identity underlying morphisms of abelian sheaves. -/
lemma exchangeCompatible_adicLowerStarCompCondensedModIso {S T : Scheme.{u}} (a : S ⟶ T)
    (b : T ⟶ T) (c : S ⟶ S) (h : a ≫ b = c ≫ a) :
    Endofunctor.IsoAlgebra.ExchangeCompatible
      (adicLowerStarComp l a b ≪≫ adicLowerStarCongr l h ≪≫ (adicLowerStarComp l c a).symm)
      (adicLowerStarCompCondensedModIso l c) (adicLowerStarCompCondensedModIso l b)
      (CondensedRing.lowerStarComp _ a b ≪≫ CondensedRing.lowerStarCongr _ h ≪≫
          (CondensedRing.lowerStarComp _ c a).symm)
      (adicLowerStarCompCondensedModIso l a) := by
  intro M
  refine Mod.Hom.ext ?_
  simp only [Mod.comp_hom', Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [adicLowerStarCompCondensedModIso_hom_app_hom, CondensedRing.lowerStar_map_hom]
  simp only [CondensedRing.lowerStarComp_hom_app_hom, CondensedRing.lowerStarCongr_hom_app_hom,
    CondensedRing.lowerStarComp_inv_app_hom]
  simp only [adicSheafEquivCondensedMod_functor_map_hom, Mod.comp_hom', Functor.map_comp]
  rw [adicLowerStarCongr_hom_app_hom, adicLowerStarComp_hom_app_hom, adicLowerStarComp_inv_app_hom,
    weilCoefficientsForgetAb_map_lowerStarComp_hom_app,
    weilCoefficientsForgetAb_map_lowerStarCongr_hom_app,
    weilCoefficientsForgetAb_map_lowerStarComp_inv_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  refine (Category.id_comp _).trans ((Category.id_comp _).trans (Eq.trans ?_
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (Category.comp_id _)).trans
      (Category.comp_id _))).symm))
  exact congrArg₂ (· ≫ ·) (lowerStarComp_hom_app_adicSheafEquivCondensedMod_obj_X l a b M).symm
    (congrArg₂ (· ≫ ·) (lowerStarCongr_hom_app_adicSheafEquivCondensedMod_obj_X l h M).symm
      (lowerStarComp_inv_app_adicSheafEquivCondensedMod_obj_X l c a M).symm)

end AlgebraicGeometry.ProEtale

/-! ### Weil pushforward, pullback and extension by zero in the condensed model -/

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)

/-- The pushforward of module objects over `Λ` along the base change `φ̄` commutes with the
Frobenius pullbacks `(Fr⁻¹)_*`: both composites are the pushforward along
`φ̄ ≫ Fr_Y⁻¹ = Fr_X⁻¹ ≫ φ̄`. This is the new-model counterpart of
`AlgebraicGeometry.ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def lowerStarGeometricFiberMapCompFrobeniusIso :
    lowerStar Λ (Scheme.Hom.geometricFiberMap φ h) ⋙
        lowerStar Λ g.geometricGaloisFrobenius.asIso.inv ≅
      lowerStar Λ f.geometricGaloisFrobenius.asIso.inv ⋙
        lowerStar Λ (Scheme.Hom.geometricFiberMap φ h) :=
  lowerStarComp Λ _ _ ≪≫
    lowerStarCongr Λ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h) ≪≫
    (lowerStarComp Λ _ _).symm

/-- The pushforward `φ_*` of condensed Weil objects (module objects `M` over `Λ` on the geometric
fibre with an isomorphism `(Fr⁻¹)_* M ≅ M`): the pushforward along the base change `φ̄`, with the
Weil structure transported along
`AlgebraicGeometry.ProEtale.CondensedRing.lowerStarGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def geometricFiberMapWeilLowerStar :
    Endofunctor.IsoAlgebra (lowerStar Λ f.geometricGaloisFrobenius.asIso.inv) ⥤
      Endofunctor.IsoAlgebra (lowerStar Λ g.geometricGaloisFrobenius.asIso.inv) :=
  Endofunctor.IsoAlgebra.mapOfNatIso (lowerStarGeometricFiberMapCompFrobeniusIso Λ φ h)

instance : (geometricFiberMapWeilLowerStar Λ φ h).Additive :=
  Endofunctor.IsoAlgebra.additive_mapOfNatIso _

/-- The exchange isomorphism `φ̄^* ⋙ (Fr_X⁻¹)_* ≅ (Fr_Y⁻¹)_* ⋙ φ̄^*` of the pullback, the mate of
`AlgebraicGeometry.ProEtale.CondensedRing.lowerStarGeometricFiberMapCompFrobeniusIso` under
`φ̄^* ⊣ φ̄_*`. -/
noncomputable def upperStarGeometricFiberMapCompFrobeniusIso :
    upperStar Λ (Scheme.Hom.geometricFiberMap φ h) ⋙
        lowerStar Λ f.geometricGaloisFrobenius.asIso.inv ≅
      lowerStar Λ g.geometricGaloisFrobenius.asIso.inv ⋙
        upperStar Λ (Scheme.Hom.geometricFiberMap φ h) :=
  Endofunctor.IsoAlgebra.leftMateIso (upperStarLowerStarAdjunction Λ _)
    (lowerStarGeometricFiberMapCompFrobeniusIso Λ φ h)

/-- The pullback `φ^*` of condensed Weil objects: the pullback along the base change `φ̄`, with
the Weil structure transported along the mate of the exchange isomorphism of the pushforward. -/
noncomputable def geometricFiberMapWeilUpperStar :
    Endofunctor.IsoAlgebra (lowerStar Λ g.geometricGaloisFrobenius.asIso.inv) ⥤
      Endofunctor.IsoAlgebra (lowerStar Λ f.geometricGaloisFrobenius.asIso.inv) :=
  Endofunctor.IsoAlgebra.mapOfNatIso (upperStarGeometricFiberMapCompFrobeniusIso Λ φ h)

instance : (geometricFiberMapWeilUpperStar Λ φ h).Additive :=
  Endofunctor.IsoAlgebra.additive_mapOfNatIso _

instance : PreservesFiniteLimits (geometricFiberMapWeilUpperStar Λ φ h) :=
  Endofunctor.IsoAlgebra.preservesFiniteLimits_mapOfNatIso _

instance : PreservesFiniteColimits (geometricFiberMapWeilUpperStar Λ φ h) :=
  Endofunctor.IsoAlgebra.preservesFiniteColimits_mapOfNatIso _

/-- The adjunction `φ^* ⊣ φ_*` of condensed Weil objects, lifted from `φ̄^* ⊣ φ̄_*`. -/
noncomputable def weilUpperStarLowerStarAdjunction :
    geometricFiberMapWeilUpperStar Λ φ h ⊣ geometricFiberMapWeilLowerStar Λ φ h :=
  Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction (upperStarLowerStarAdjunction Λ _) _ _
    (Endofunctor.IsoAlgebra.mateEquiv_leftMateIso_inv _ _)

section OpenImmersion

variable [IsOpenImmersion φ]

/-- The exchange isomorphism `φ̄_! ⋙ (Fr_Y⁻¹)_* ≅ (Fr_X⁻¹)_* ⋙ φ̄_!` of the extension by zero
along the base change of an open immersion, the mate of
`AlgebraicGeometry.ProEtale.CondensedRing.upperStarGeometricFiberMapCompFrobeniusIso` under
`φ̄_! ⊣ φ̄^*`. -/
noncomputable def openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso :
    openImmersionLowerShriek Λ (Scheme.Hom.geometricFiberMap φ h) ⋙
        lowerStar Λ g.geometricGaloisFrobenius.asIso.inv ≅
      lowerStar Λ f.geometricGaloisFrobenius.asIso.inv ⋙
        openImmersionLowerShriek Λ (Scheme.Hom.geometricFiberMap φ h) :=
  Endofunctor.IsoAlgebra.leftMateIso (openImmersionLowerShriekUpperStarAdjunction Λ _)
    (upperStarGeometricFiberMapCompFrobeniusIso Λ φ h)

/-- Extension by zero `φ_!` of condensed Weil objects along an open immersion `φ`: the extension
by zero along the base change `φ̄`, with the transported Weil structure. -/
noncomputable def weilExtensionByZero :
    Endofunctor.IsoAlgebra (lowerStar Λ f.geometricGaloisFrobenius.asIso.inv) ⥤
      Endofunctor.IsoAlgebra (lowerStar Λ g.geometricGaloisFrobenius.asIso.inv) :=
  Endofunctor.IsoAlgebra.mapOfNatIso
    (openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso Λ φ h)

instance : (weilExtensionByZero Λ φ h).Additive :=
  Endofunctor.IsoAlgebra.additive_mapOfNatIso _

instance : PreservesFiniteLimits (weilExtensionByZero Λ φ h) :=
  Endofunctor.IsoAlgebra.preservesFiniteLimits_mapOfNatIso _

instance : PreservesFiniteColimits (weilExtensionByZero Λ φ h) :=
  Endofunctor.IsoAlgebra.preservesFiniteColimits_mapOfNatIso _

/-- The adjunction `φ_! ⊣ φ^*` of condensed Weil objects along an open immersion, lifted from
`φ̄_! ⊣ φ̄^*`. -/
noncomputable def weilExtensionByZeroUpperStarAdjunction :
    weilExtensionByZero Λ φ h ⊣ geometricFiberMapWeilUpperStar Λ φ h :=
  Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction (openImmersionLowerShriekUpperStarAdjunction Λ _)
    _ _ (Endofunctor.IsoAlgebra.mateEquiv_leftMateIso_inv _ _)

end OpenImmersion

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}}
  {f : X₀ ⟶ Spec (.of k)} {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)

/-- The pushforward compatibility of the two models along the base change `φ̄` is compatible
with the Frobenius exchange isomorphisms
`AlgebraicGeometry.ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso` and
`AlgebraicGeometry.ProEtale.CondensedRing.lowerStarGeometricFiberMapCompFrobeniusIso`. -/
lemma exchangeCompatible_lowerStar_geometricFiberMap :
    Endofunctor.IsoAlgebra.ExchangeCompatible
      (adicLowerStarGeometricFiberMapCompFrobeniusIso l φ h)
      (adicLowerStarCompCondensedModIso l f.geometricGaloisFrobenius.asIso.inv)
      (adicLowerStarCompCondensedModIso l g.geometricGaloisFrobenius.asIso.inv)
      (CondensedRing.lowerStarGeometricFiberMapCompFrobeniusIso _ φ h)
      (adicLowerStarCompCondensedModIso l (Scheme.Hom.geometricFiberMap φ h)) :=
  exchangeCompatible_adicLowerStarCompCondensedModIso l _ _ _
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h)

end AlgebraicGeometry.ProEtale

/-! ### Comparison of the Weil functors of the two models -/

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- **Pushforward of Weil sheaves in the two models**: the equivalences
`AlgebraicGeometry.ProEtaleWeilSheaf.toCondensed` intertwine the pushforward of pro-étale Weil
sheaves with the pushforward of condensed Weil objects. It is the pushforward compatibility
`AlgebraicGeometry.ProEtale.adicLowerStarCompCondensedModIso` along the base change `φ̄`, which is
compatible with the Frobenius structures
(`AlgebraicGeometry.ProEtale.exchangeCompatible_lowerStar_geometricFiberMap`). -/
noncomputable def lowerStarCompToCondensedIso (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] :
    lowerStar k₀ l φ ⋙ toCondensed k₀ l Y ≅
      toCondensed k₀ l X ⋙
        CondensedRing.geometricFiberMapWeilLowerStar (Profinite.padicAlgClRingObj l) φ
          (comp_over φ _) :=
  Endofunctor.IsoAlgebra.mapOfNatIsoCompIsoOfExchange _
    (exchangeCompatible_lowerStar_geometricFiberMap l φ (comp_over φ _))

variable (k₀ l) in
/-- **Pullback of Weil sheaves in the two models**: the equivalences
`AlgebraicGeometry.ProEtaleWeilSheaf.toCondensed` intertwine the pullback of pro-étale Weil
sheaves with the pullback of condensed Weil objects. Both are left adjoint to the pushforwards,
so this is the conjugate of
`AlgebraicGeometry.ProEtaleWeilSheaf.lowerStarCompToCondensedIso`. -/
noncomputable def upperStarCompToCondensedIso (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] :
    upperStar k₀ l φ ⋙ toCondensed k₀ l X ≅
      toCondensed k₀ l Y ⋙
        CondensedRing.geometricFiberMapWeilUpperStar (Profinite.padicAlgClRingObj l) φ
          (comp_over φ _) :=
  Adjunction.leftAdjointCompIsoOfEquivalence (upperStarLowerStarAdjunction k₀ l φ)
    (CondensedRing.weilUpperStarLowerStarAdjunction _ φ _) (toCondensed k₀ l X).asEquivalence
    (toCondensed k₀ l Y).asEquivalence (lowerStarCompToCondensedIso k₀ l φ)

variable (k₀ l) in
/-- **Extension by zero of Weil sheaves in the two models**: for an open immersion `j`, the
equivalences `AlgebraicGeometry.ProEtaleWeilSheaf.toCondensed` intertwine the extension by zero of
pro-étale Weil sheaves with that of condensed Weil objects. Both are left adjoint to the
pullbacks, so this is the conjugate of
`AlgebraicGeometry.ProEtaleWeilSheaf.upperStarCompToCondensedIso`. -/
noncomputable def extensionByZeroCompToCondensedIso (j : X ⟶ Y) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    extensionByZero k₀ l j ⋙ toCondensed k₀ l Y ≅
      toCondensed k₀ l X ⋙
        CondensedRing.weilExtensionByZero (Profinite.padicAlgClRingObj l) j (comp_over j _) :=
  Adjunction.leftAdjointCompIsoOfEquivalence (extensionByZeroUpperStarAdjunction k₀ l j)
    (CondensedRing.weilExtensionByZeroUpperStarAdjunction _ j _)
    (toCondensed k₀ l Y).asEquivalence (toCondensed k₀ l X).asEquivalence
    (upperStarCompToCondensedIso k₀ l j)

/-! ### The derived equivalence and the derived functors -/

variable (k₀ l X) in
/-- The equivalence `AlgebraicGeometry.ProEtaleWeilSheaf.toCondensed` from pro-étale Weil sheaves of
the old model to condensed Weil objects. -/
noncomputable def condensedEquivalence :
    ProEtaleWeilSheaf k₀ l X ≌ Endofunctor.IsoAlgebra
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv) :=
  (toCondensed k₀ l X).asEquivalence

lemma condensedEquivalence_functor :
    (condensedEquivalence k₀ l X).functor = toCondensed k₀ l X :=
  rfl

instance : (condensedEquivalence k₀ l X).functor.Additive :=
  inferInstanceAs (toCondensed k₀ l X).Additive

instance : (condensedEquivalence k₀ l X).inverse.Additive :=
  inferInstance

variable (k₀ l X) in
/-- **Derived categories of Weil sheaves in the two models**: the equivalence
`AlgebraicGeometry.ProEtaleWeilSheaf.toCondensed` of abelian categories induces an equivalence
between the derived category of pro-étale Weil sheaves on `X̄` and the derived category of
condensed `ℚ̲̄_ℓ`-modules on `X̄` with an isomorphism `(Fr_X⁻¹)_* M ≅ M`. -/
noncomputable def derivedEquivCondensed :
    _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l X) ≌
      _root_.DerivedCategory (Endofunctor.IsoAlgebra
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)) :=
  (condensedEquivalence k₀ l X).mapDerivedCategory

lemma derivedEquivCondensed_functor :
    (derivedEquivCondensed k₀ l X).functor = (toCondensed k₀ l X).mapDerivedCategory :=
  rfl

/-- The derived comparison commutes with the shifts. -/
noncomputable instance : (derivedEquivCondensed k₀ l X).functor.CommShift ℤ :=
  inferInstanceAs ((toCondensed k₀ l X).mapDerivedCategory.CommShift ℤ)

/-- The derived comparison is a triangulated functor. -/
instance : (derivedEquivCondensed k₀ l X).functor.IsTriangulated :=
  inferInstanceAs ((toCondensed k₀ l X).mapDerivedCategory.IsTriangulated)

variable (k₀ l X) in
/-- The derived comparison commutes with the cohomology objects:
`E (Hⁿ K) ≅ Hⁿ (D(E) K)`. -/
noncomputable def homologyFunctorCompToCondensedIso (n : ℤ) :
    _root_.DerivedCategory.homologyFunctor (ProEtaleWeilSheaf k₀ l X) n ⋙ toCondensed k₀ l X ≅
      (derivedEquivCondensed k₀ l X).functor ⋙ _root_.DerivedCategory.homologyFunctor _ n :=
  Functor.mapDerivedCategoryHomologyFunctorIso _ n

variable (k₀ l) in
/-- **Derived pushforward of Weil sheaves in the two models**: `Rφ_* ⋙ D(E) ≅ D(E) ⋙ Rφ_*`, from
the underived compatibility
`AlgebraicGeometry.ProEtaleWeilSheaf.lowerStarCompToCondensedIso`. -/
noncomputable def rightDerivedLowerStarCompToCondensedIso (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] :
    (lowerStar k₀ l φ).rightDerivedFunctor ⋙ (derivedEquivCondensed k₀ l Y).functor ≅
      (derivedEquivCondensed k₀ l X).functor ⋙
        (CondensedRing.geometricFiberMapWeilLowerStar (Profinite.padicAlgClRingObj l) φ
          (comp_over φ _)).rightDerivedFunctor :=
  Functor.rightDerivedFunctorCompMapDerivedCategoryIsoOfEquivalence
    (condensedEquivalence k₀ l X) (condensedEquivalence k₀ l Y)
    (lowerStarCompToCondensedIso k₀ l φ)

variable (k₀ l X) in
/-- The derived comparison commutes with the embeddings in degree `n`:
`D(E) (F[-n]) ≅ (E F)[-n]`. -/
noncomputable def singleFunctorCompDerivedEquivCondensedIso (n : ℤ) :
    _root_.DerivedCategory.singleFunctor (ProEtaleWeilSheaf k₀ l X) n ⋙
        (derivedEquivCondensed k₀ l X).functor ≅
      toCondensed k₀ l X ⋙ _root_.DerivedCategory.singleFunctor _ n :=
  Functor.mapDerivedCategorySingleFunctor _ n

variable (k₀ l) in
/-- **Derived pullback of Weil sheaves in the two models**: `D(φ^*) ⋙ D(E) ≅ D(E) ⋙ D(φ^*)`,
both pullbacks being exact. -/
noncomputable def upperStarMapDerivedCategoryCompIso (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] :
    (upperStar k₀ l φ).mapDerivedCategory ⋙ (derivedEquivCondensed k₀ l X).functor ≅
      (derivedEquivCondensed k₀ l Y).functor ⋙
        (CondensedRing.geometricFiberMapWeilUpperStar (Profinite.padicAlgClRingObj l) φ
          (comp_over φ _)).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIsoOfIso (upperStarCompToCondensedIso k₀ l φ)

variable (k₀ l) in
/-- **Derived extension by zero of Weil sheaves in the two models**:
`D(j_!) ⋙ D(E) ≅ D(E) ⋙ D(j_!)`, both extensions by zero being exact. -/
noncomputable def extensionByZeroMapDerivedCategoryCompIso (j : X ⟶ Y) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    (extensionByZero k₀ l j).mapDerivedCategory ⋙ (derivedEquivCondensed k₀ l Y).functor ≅
      (derivedEquivCondensed k₀ l X).functor ⋙
        (CondensedRing.weilExtensionByZero (Profinite.padicAlgClRingObj l) j
          (comp_over j _)).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIsoOfIso (extensionByZeroCompToCondensedIso k₀ l j)

attribute [local instance] Compactification.over

variable (k₀ l) in
/-- The direct image with compact support `Rf_! = Rḡ_* ∘ D(ī_!)` of condensed Weil objects
attached to a compactification `X ⟶[i] Z ⟶[g] Y` of a morphism of `k₀`-schemes: the new-model
counterpart of `AlgebraicGeometry.ProEtaleWeilSheaf.rightDerivedLowerShriek`. -/
noncomputable def condensedRightDerivedLowerShriek (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] (c : Compactification f) :
    _root_.DerivedCategory (Endofunctor.IsoAlgebra
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)) ⥤
      _root_.DerivedCategory (Endofunctor.IsoAlgebra
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
          (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)) :=
  (CondensedRing.weilExtensionByZero (Profinite.padicAlgClRingObj l) c.i
      (comp_over c.i _)).mapDerivedCategory ⋙
    (CondensedRing.geometricFiberMapWeilLowerStar (Profinite.padicAlgClRingObj l) c.g
      (comp_over c.g _)).rightDerivedFunctor

variable (k₀ l) in
/-- **Direct image with compact support of Weil sheaves in the two models**: for a
compactification `c` of `f`, `Rf_! ⋙ D(E) ≅ D(E) ⋙ Rf_!`, where the old `Rf_!` is
`AlgebraicGeometry.ProEtaleWeilSheaf.rightDerivedLowerShriek` and the new one is
`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRightDerivedLowerShriek`. -/
noncomputable def rightDerivedLowerShriekCompIso (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] (c : Compactification f) :
    rightDerivedLowerShriek k₀ l f c ⋙ (derivedEquivCondensed k₀ l Y).functor ≅
      (derivedEquivCondensed k₀ l X).functor ⋙ condensedRightDerivedLowerShriek k₀ l f c :=
  Functor.associator (extensionByZero k₀ l c.i).mapDerivedCategory
      (lowerStar k₀ l c.g).rightDerivedFunctor _ ≪≫
    Functor.isoWhiskerLeft _ (rightDerivedLowerStarCompToCondensedIso k₀ l c.g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (extensionByZeroMapDerivedCategoryCompIso k₀ l c.i) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.ProEtaleWeilSheaf

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- **The total derived direct image with compact support of Weil complexes in the two
models**: `WeilComplex.derivedLowerShriek`, followed by the inclusion in the derived category of
pro-étale Weil sheaves and the derived comparison `D(E)`, is the inclusion followed by `D(E)` and
the new-model `Rf_!` for the same (chosen) compactification. -/
noncomputable def derivedLowerShriekCompToCondensedIso (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] :
    derivedLowerShriek k₀ l f ⋙ (objectProperty k₀ l Y).ι ⋙
        (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor ≅
      (objectProperty k₀ l X).ι ⋙ (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor ⋙
        ProEtaleWeilSheaf.condensedRightDerivedLowerShriek k₀ l f
          (HasCompactification.compactification f
            (hf := hasCompactification_of_over (k₀ := k₀) f)) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ProEtaleWeilSheaf.rightDerivedLowerShriekCompIso k₀ l f _)

end AlgebraicGeometry.WeilComplex
