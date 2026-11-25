/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleExchangeFormalism
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekCompositionPadicAlgCl
public import WeilConjectures.CategoryTheory.ExchangeFormalism.Shriek
public import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons

/-!

# The base change morphisms of bounded constructible complexes in the exchange formalism

The pullback comparison of a commutative square, the base-change morphism `Lg^* Rf_* ⟶ Rf'_* Lg'^*`
and the extension-by-zero exchange morphism `Lg'^* j'_! ⟶ j_! Lg^*` on bounded constructible
complexes are the square isomorphism, the base change map of the pushforwards and the base change
map of the extension by zero of the exchange formalism
`ProEtale.CondensedRing.boundedConstructibleExchangeFormalism`. This file records these
identifications, through which the formal coherence results of `CategoryTheory.ExchangeFormalism`
apply to them.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']

/-- The exchange morphism `exchangeLeft` is the inverse mate of the forward morphism. -/
lemma exchangeLeft_eq_mateEquiv_symm {jS : A ⥤ B} {jU : B ⥤ A} {jS' : A' ⥤ B'}
    {jU' : B' ⥤ A'} {H : A ⥤ A'} {H' : B ⥤ B'} (aj : jS ⊣ jU) (aj' : jS' ⊣ jU')
    (θ : jU ⋙ H ≅ H' ⋙ jU') :
    exchangeLeft aj aj' θ = ((mateEquiv aj aj').symm θ.hom) := by
  ext K
  simp [exchangeLeft_app, mateEquiv]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The formalism `boundedConstructibleExchangeFormalism`, for `ℚ̄_ℓ`-sheaves. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism ℓ k

section Squares

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

omit [Fact (Nat.Prime (ringChar k))] in
/-- A commutative square of separated `k`-schemes of finite type is a commutative square in
`SepFinType k`. -/
lemma SepFinType.homMk_comp_homMk {A B C D : Over (Spec (.of k))} [LocallyOfFiniteType A.hom]
    [QuasiCompact A.hom] [IsSeparated A.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
    [IsSeparated B.hom] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    [LocallyOfFiniteType D.hom] [QuasiCompact D.hom] [IsSeparated D.hom] {a : A ⟶ B} {b : B ⟶ D}
    {c : A ⟶ C} {d : C ⟶ D} (w : a ≫ b = c ≫ d) :
    SepFinType.homMk a ≫ SepFinType.homMk b = SepFinType.homMk c ≫ SepFinType.homMk d :=
  ObjectProperty.hom_ext _ w

/-- The pullback comparison `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` of a commutative square is the square
isomorphism of the exchange formalism. -/
lemma boundedConstructiblePullbackSquareComparison_eq_sqIso (sq : CommSq g' f' f g) :
    boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq =
      (𝔽).sqIso (SepFinType.homMk f') (SepFinType.homMk g') (SepFinType.homMk g)
        (SepFinType.homMk f) (SepFinType.homMk_comp_homMk sq.w.symm) := by
  rw [ExchangeFormalism.sqIso, ExchangeFormalism.pbComp'_rfl]
  unfold ExchangeFormalism.pbComp' boundedConstructiblePullbackSquareComparison
  rfl

/-- The base-change morphism `Lg^* Rf_* ⟶ Rf'_* Lg'^*` of a commutative square is the base
change map of the pushforwards of the exchange formalism. -/
lemma boundedConstructibleBaseChange_eq_pfBaseChange (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange ℓ sq =
      ((𝔽).pfBaseChange (SepFinType.homMk g') (SepFinType.homMk f') (SepFinType.homMk f)
        (SepFinType.homMk g) (SepFinType.homMk_comp_homMk sq.w)) := by
  rw [boundedConstructibleBaseChange_eq_exchangeRight, Adjunction.exchangeRight_eq_mateEquiv,
    ExchangeFormalism.pfBaseChange, boundedConstructiblePullbackSquareComparison_eq_sqIso,
    ← Iso.symm_hom, ExchangeFormalism.sqIso_symm]
  rfl

variable [IsOpenImmersion f.left] [IsOpenImmersion f'.left]

/-- The extension-by-zero exchange morphism `Lg'^* ⋙ f'_! ⟶ f_! ⋙ Lg^*` of a commutative square
of open immersions is the base change map of the extension by zero of the exchange formalism. -/
lemma boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_baseChange
    (sq : CommSq g' f' f g) :
    boundedConstructibleOpenImmersionLowerShriekBaseChange' (Profinite.padicAlgClRingObj ℓ) ℓ sq =
      ((𝔽).baseChange (SepFinType.homMk g') (SepFinType.homMk f') (SepFinType.homMk f)
        (SepFinType.homMk g) (SepFinType.homMk_comp_homMk sq.w)) := by
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft,
    Adjunction.exchangeLeft_eq_mateEquiv_symm, ExchangeFormalism.baseChange,
    boundedConstructiblePullbackSquareComparison_eq_sqIso]
  rfl

/-- The two definitions of the extension-by-zero exchange morphism agree. -/
lemma boundedConstructibleOpenImmersionLowerShriekBaseChange_eq' (sq : CommSq g' f' f g) :
    boundedConstructibleOpenImmersionLowerShriekBaseChange (Profinite.padicAlgClRingObj ℓ) ℓ sq =
      boundedConstructibleOpenImmersionLowerShriekBaseChange' (Profinite.padicAlgClRingObj ℓ) ℓ sq
          := by
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_exchangeLeft,
    boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft]

/-- The extension-by-zero exchange morphism `Lg'^* ⋙ f'_! ⟶ f_! ⋙ Lg^*` of a commutative square
of open immersions is the base change map of the extension by zero of the exchange formalism. -/
lemma boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_baseChange
    (sq : CommSq g' f' f g) :
    boundedConstructibleOpenImmersionLowerShriekBaseChange (Profinite.padicAlgClRingObj ℓ) ℓ sq =
      ((𝔽).baseChange (SepFinType.homMk g') (SepFinType.homMk f') (SepFinType.homMk f)
        (SepFinType.homMk g) (SepFinType.homMk_comp_homMk sq.w)) := by
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChange_eq',
    boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_baseChange]

/-- Base change for extension by zero in the exchange formalism: the base change map of a
cartesian square of open immersions is an isomorphism. -/
lemma isIso_baseChange_boundedConstructibleExchangeFormalism (sq : IsPullback g' f' f g) :
    IsIso ((𝔽).baseChange (SepFinType.homMk g') (SepFinType.homMk f') (SepFinType.homMk f)
      (SepFinType.homMk g) (SepFinType.homMk_comp_homMk sq.w)) := by
  rw [← boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_baseChange]
  exact isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange' (Profinite.padicAlgClRingObj
      ℓ) ℓ sq

/-- The extension-by-zero base-change isomorphism `f_! ⋙ Lg^* ≅ Lg'^* ⋙ f'_!` of a cartesian
square is the inverse of the base change map of the extension by zero of the exchange formalism. -/
lemma boundedConstructibleOpenImmersionLowerShriekBaseChangeIso_hom_eq
    (sq : IsPullback g' f' f g) :
    haveI := isIso_baseChange_boundedConstructibleExchangeFormalism ℓ sq
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso (Profinite.padicAlgClRingObj ℓ) ℓ
        sq).hom =
      inv ((𝔽).baseChange (SepFinType.homMk g') (SepFinType.homMk f') (SepFinType.homMk f)
        (SepFinType.homMk g) (SepFinType.homMk_comp_homMk sq.w)) := by
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChangeIso, Iso.symm_hom, asIso_inv]
  simp only [boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_baseChange]

end Squares

section Composition

variable {X Y Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` is the composition isomorphism of the
pushforwards of the exchange formalism. -/
lemma boundedConstructibleLowerStarComp_eq_pfComp' (f : X ⟶ Y) (g : Y ⟶ Z) :
    boundedConstructibleLowerStarComp ℓ f g =
      ((𝔽).pfComp' (SepFinType.homMk f) (SepFinType.homMk g)
        (SepFinType.homMk f ≫ SepFinType.homMk g) rfl).symm := by
  rw [ExchangeFormalism.pfComp', ExchangeFormalism.pbComp'_rfl]
  rfl

/-- The identity isomorphism `R(𝟙 X)_* ≅ 𝟭` is the identity isomorphism of the pushforwards of
the exchange formalism. -/
lemma boundedConstructibleLowerStarId_eq_pfId :
    boundedConstructibleLowerStarId ℓ X = (𝔽).pfId (SepFinType.mk X) :=
  rfl

end Composition

section Shriek

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

/-- The lower shriek attached to a compactification is the compactly supported direct image of
the exchange formalism. -/
lemma boundedConstructibleLowerShriekOfCompactification_eq_shriek (c : Compactification f.left) :
    boundedConstructibleLowerShriekOfCompactification ℓ c =
      (𝔽).shriek (SepFinType.homMk c.overI) (SepFinType.homMk c.overG) :=
  rfl

end Shriek

section Exchange

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z} [IsOpenImmersion i'.left]
  [IsOpenImmersion j.left]

/-- The exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of a cartesian square is the exchange map
of the exchange formalism. -/
lemma boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_eq_exchange
    (sq : IsPullback p i' j p') :
    haveI := isIso_baseChange_boundedConstructibleExchangeFormalism ℓ sq
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ sq =
      ((𝔽).exchange (SepFinType.homMk p) (SepFinType.homMk i') (SepFinType.homMk j)
        (SepFinType.homMk p') (SepFinType.homMk_comp_homMk sq.w)) := by
  rw [boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_eq_exchangeRight,
    Adjunction.exchangeRight_eq_mateEquiv, ExchangeFormalism.exchange]
  congr 2
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChangeIso', Iso.symm_hom, asIso_inv]
  simp only [boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_baseChange]

end Exchange

section Refinement

variable {X Z Z₁ Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]

/-- Base change for extension by zero in the exchange formalism, for a cartesian square with an
identity as top side. -/
lemma isIso_baseChange_boundedConstructibleExchangeFormalism_id (sq : IsPullback (𝟙 X) i i₁ h) :
    IsIso ((𝔽).baseChange (𝟙 (SepFinType.mk X)) (SepFinType.homMk i) (SepFinType.homMk i₁)
      (SepFinType.homMk h) (SepFinType.homMk_comp_homMk (a := 𝟙 X) sq.w)) :=
  isIso_baseChange_boundedConstructibleExchangeFormalism ℓ sq

/-- The inverse of the composition isomorphism of the pushforwards of the exchange formalism
along `h ≫ p₁` is the composition isomorphism `Rh_* ⋙ Rp₁_* ≅ R(h ≫ p₁)_*`. -/
lemma pfComp'_homMk_comp_inv {p₁ : Z₁ ⟶ Y} (hp : SepFinType.homMk h ≫ SepFinType.homMk p₁ =
      SepFinType.homMk (h ≫ p₁)) :
    ((𝔽).pfComp' (SepFinType.homMk h) (SepFinType.homMk p₁) (SepFinType.homMk (h ≫ p₁))
      hp).inv = (boundedConstructibleLowerStarComp ℓ h p₁).hom := by
  rw [show (𝔽).pfComp' (SepFinType.homMk h) (SepFinType.homMk p₁)
      (SepFinType.homMk (h ≫ p₁)) hp =
    (𝔽).pfComp' (SepFinType.homMk h) (SepFinType.homMk p₁)
      (SepFinType.homMk h ≫ SepFinType.homMk p₁) rfl from rfl,
    boundedConstructibleLowerStarComp_eq_pfComp']
  rfl

/-- The comparison isomorphism `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` along a refinement
(`boundedConstructibleLowerShriekRefinementIso'`) is the comparison along a refinement of the
exchange formalism. -/
lemma boundedConstructibleLowerShriekRefinementIso'_hom_eq (sq : IsPullback (𝟙 X) i i₁ h)
    {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} (wp : h ≫ p₁ = p)
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ sq)] :
    haveI := isIso_baseChange_boundedConstructibleExchangeFormalism_id ℓ sq
    (boundedConstructibleLowerShriekRefinementIso' ℓ sq wp).hom =
      (𝔽).refinementComparison (SepFinType.homMk i) (SepFinType.homMk p) (SepFinType.homMk i₁)
        (SepFinType.homMk p₁) (SepFinType.homMk h) (SepFinType.homMk_comp_homMk (a := 𝟙 X) sq.w)
        (ObjectProperty.hom_ext _ wp) := by
  subst wp
  refine NatTrans.ext (funext fun K ↦ ?_)
  rw [ExchangeFormalism.refinementComparison_app, pfComp'_homMk_comp_inv]
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id,
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_eq_exchange,
    boundedConstructibleLowerShriekRefinementIso', Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom, asIso_hom,
    Functor.associator_hom_app, Category.id_comp, Functor.map_comp, Functor.leftUnitor_inv_app,
    Category.assoc]
  rfl

/-- The restriction comparison `i_! ⟶ i₁_! ⋙ Lh^*` is the exchange morphism of the triangle
comparison. -/
lemma boundedConstructibleOpenImmersionLowerShriekRefinement_eq_exchangeLeft (w : i ≫ h = i₁) :
    boundedConstructibleOpenImmersionLowerShriekRefinement (Profinite.padicAlgClRingObj ℓ) ℓ w =
      Adjunction.exchangeLeft
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
            (Profinite.padicAlgClRingObj ℓ) ℓ i₁)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
            (Profinite.padicAlgClRingObj ℓ) ℓ i)
        (Functor.rightUnitor _ ≪≫ boundedConstructibleUpperStarTriangleComparison
            (Profinite.padicAlgClRingObj ℓ) ℓ w) := by
  unfold boundedConstructibleOpenImmersionLowerShriekRefinement
    boundedConstructibleOpenImmersionLowerShriekRefinementUnitStep
    boundedConstructibleOpenImmersionLowerShriekRefinementTriangleStep
    boundedConstructibleOpenImmersionLowerShriekRefinementCounitStep Adjunction.exchangeLeft
  rfl

omit [IsOpenImmersion i.left] [IsOpenImmersion i₁.left] in
/-- The triangle comparison `Li₁^* ≅ Lh^* ⋙ Li^*` is the composition isomorphism of the
pullbacks of the exchange formalism. -/
lemma boundedConstructibleUpperStarTriangleComparison_eq_pbComp' (w : i ≫ h = i₁) :
    boundedConstructibleUpperStarTriangleComparison (Profinite.padicAlgClRingObj ℓ) ℓ w =
      (boundedConstructibleExchangeFormalism ℓ k).pbComp' (SepFinType.homMk i)
        (SepFinType.homMk h) (SepFinType.homMk i₁) (ObjectProperty.hom_ext _ w) :=
  rfl

/-- The comparison isomorphism `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` along a refinement
(`boundedConstructibleLowerShriekRefinementIso`) is the comparison along a refinement of the
exchange formalism. -/
lemma boundedConstructibleLowerShriekRefinementIso_hom_eq (sq : IsPullback (𝟙 X) i i₁ h)
    {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} (wp : h ≫ p₁ = p)
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ sq)] :
    haveI := isIso_baseChange_boundedConstructibleExchangeFormalism_id ℓ sq
    (boundedConstructibleLowerShriekRefinementIso ℓ sq wp).hom =
      (𝔽).refinementComparison (SepFinType.homMk i) (SepFinType.homMk p) (SepFinType.homMk i₁)
        (SepFinType.homMk p₁) (SepFinType.homMk h) (SepFinType.homMk_comp_homMk (a := 𝟙 X) sq.w)
        (ObjectProperty.hom_ext _ wp) := by
  subst wp
  have hw : i ≫ h = i₁ := sq.toCommSq.snd_comp_eq_of_fst_eq_id
  have hR := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement
      (Profinite.padicAlgClRingObj ℓ) ℓ sq
  have := isIso_baseChange_boundedConstructibleExchangeFormalism_id ℓ sq
  have : IsIso (Adjunction.exchangeLeft ((𝔽).shAdj (SepFinType.homMk i₁))
      ((𝔽).shAdj (SepFinType.homMk i)) (Functor.rightUnitor ((𝔽).pb (SepFinType.homMk i₁)) ≪≫
        (𝔽).pbComp' (SepFinType.homMk i) (SepFinType.homMk h) (SepFinType.homMk i₁)
          (ObjectProperty.hom_ext _ hw))) := by
    rwa [boundedConstructibleOpenImmersionLowerShriekRefinement_eq_exchangeLeft,
      boundedConstructibleUpperStarTriangleComparison_eq_pbComp'] at hR
  rw [ExchangeFormalism.refinementComparison_eq_exchangeLeft _ _ _ _ _ _ _ _
    (ObjectProperty.hom_ext _ hw)]
  refine NatTrans.ext (funext fun K ↦ ?_)
  simp only [boundedConstructibleLowerShriekRefinementIso,
    boundedConstructibleOpenImmersionLowerShriekRefinementPushforward,
    boundedConstructibleOpenImmersionLowerShriekRefinement_eq_exchangeLeft,
    boundedConstructibleUpperStarTriangleComparison_eq_pbComp', pfComp'_homMk_comp_inv,
    eqToIso_refl, Iso.refl_hom, Category.comp_id, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, asIso_hom, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Functor.map_comp, Functor.rightUnitor_inv_app, Category.assoc,
    Functor.comp_obj, Functor.comp_map]
  rfl

/-- The two comparison isomorphisms along a refinement agree. -/
lemma boundedConstructibleLowerShriekRefinementIso_eq' (sq : IsPullback (𝟙 X) i i₁ h)
    {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} (wp : h ≫ p₁ = p)
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ sq)]
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ sq)] :
    boundedConstructibleLowerShriekRefinementIso ℓ sq wp =
      boundedConstructibleLowerShriekRefinementIso' ℓ sq wp :=
  Iso.ext ((boundedConstructibleLowerShriekRefinementIso_hom_eq ℓ sq wp).trans
    (boundedConstructibleLowerShriekRefinementIso'_hom_eq ℓ sq wp).symm)

end Refinement

section Independence

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

/-- The two comparison isomorphisms between the lower shrieks attached to two compactifications
agree. -/
lemma boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_eq'
    (c₁ c₂ : Compactification f.left) :
    boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ c₁ c₂ =
      boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁ c₂ := by
  have := (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.isProper
  have := (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.isProper
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.isPullback
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.isPullback
  rw [boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_eq_refinementIso,
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq_refinementIso',
    boundedConstructibleLowerShriekRefinementIso_eq',
    boundedConstructibleLowerShriekRefinementIso_eq']

end Independence

section CompositionBridges

variable {X Y Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]

/-- The composition isomorphism `(j ≫ j')_! ≅ j_! ⋙ j'_!` of the extensions by zero is the
composition isomorphism of the extensions by zero of the exchange formalism. -/
lemma boundedConstructibleOpenImmersionLowerShriekComp_eq_shComp' (j : X ⟶ Y) (j' : Y ⟶ Z)
    [IsOpenImmersion j.left] [IsOpenImmersion j'.left] [IsOpenImmersion (j ≫ j').left] :
    boundedConstructibleOpenImmersionLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ j j' =
      (𝔽).shComp' (SepFinType.homMk j) (SepFinType.homMk j') (SepFinType.homMk (j ≫ j'))
        (ObjectProperty.hom_ext _ rfl) := by
  rw [ExchangeFormalism.shComp',
    show (𝔽).pbComp' (SepFinType.homMk j) (SepFinType.homMk j') (SepFinType.homMk (j ≫ j'))
      (ObjectProperty.hom_ext _ rfl) =
      (𝔽).pbComp' (SepFinType.homMk j) (SepFinType.homMk j')
        (SepFinType.homMk j ≫ SepFinType.homMk j') rfl from rfl,
    ExchangeFormalism.pbComp'_rfl]
  rfl

end CompositionBridges

section ExchangeUnprimed

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z} [IsOpenImmersion i'.left]
  [IsOpenImmersion j.left]

/-- The exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of a cartesian square is the exchange map
of the exchange formalism. -/
lemma boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_eq_exchange
    (sq : IsPullback p i' j p') :
    haveI := isIso_baseChange_boundedConstructibleExchangeFormalism ℓ sq
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ sq =
      ((𝔽).exchange (SepFinType.homMk p) (SepFinType.homMk i') (SepFinType.homMk j)
        (SepFinType.homMk p') (SepFinType.homMk_comp_homMk sq.w)) := by
  have : boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ sq =
      Adjunction.exchangeRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ p)
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ p')
        (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso (Profinite.padicAlgClRingObj ℓ) ℓ
            sq) := by
    unfold boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
      boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep
      boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep
      boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep
      Adjunction.exchangeRight
    rfl
  rw [this, Adjunction.exchangeRight_eq_mateEquiv, ExchangeFormalism.exchange,
    boundedConstructibleOpenImmersionLowerShriekBaseChangeIso_hom_eq]
  rfl

end ExchangeUnprimed

end AlgebraicGeometry.ProEtale.CondensedRing
