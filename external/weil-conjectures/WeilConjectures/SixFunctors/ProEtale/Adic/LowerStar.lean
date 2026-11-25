/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.SixFunctors.ProEtale.Adic.Abelian
public import WeilConjectures.SixFunctors.ProEtale.Adic.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Adic.Extension
public import WeilConjectures.SixFunctors.ProEtale.Adic.MayerVietoris
public import WeilConjectures.SixFunctors.ProEtale.Adic.Module

/-!
# Reductions for the finiteness of the pushforward of constructible `ℓ`-adic sheaves

Let `K` be an algebraically closed field of characteristic different from `ℓ`, `Y` a scheme
locally of finite type over `K` and `f : X ⟶ Y` a quasi-compact, quasi-separated morphism
locally of finite type. The *finiteness theorem* (SGA 4½, *Th. finitude*, Th. 1.1, with
`ℓ`-adic coefficients as in Bhatt–Scholze, *The pro-étale topology for schemes*, §6.8, and the
blueprint `proposition-six-operations-dctf` (3), the `ℚ̄_ℓ` stage of the
finite-coefficient `sk-prop-sf-finiteness`) asserts that for a constructible `ℓ`-adic sheaf `F` on
`X_proét` the derived pushforward `Rf_*(F[0])` has constructible cohomology sheaves, and is
bounded if `Y` is quasi-compact. The theorem itself is proved in
`WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarFiniteness`, by comparison with the module
objects over the condensed coefficient ring `ℚ̲̄_ℓ`. This file contains the reductions of the
general statement to an affine source and an affine target:

- the objects with bounded constructible derived pushforward form a triangulated subcategory
  (`AlgebraicGeometry.ProEtale.finiteLowerStar`), so the statement is stable under extensions,
  kernels and cokernels and extends to bounded complexes with constructible cohomology
  (`AlgebraicGeometry.ProEtale.finiteLowerStar_of_bounded`);
- the **Čech step** of `sk-prop-sf-finiteness`: a Mayer–Vietoris argument
  (`AlgebraicGeometry.ProEtale.finiteLowerStar_of_openCover`) and an induction over finite
  affine covers reduce a quasi-compact quasi-separated source to an affine one, first for a
  source with affine diagonal (`AlgebraicGeometry.ProEtale.FiniteFor.of_isAffineHom_diagonal`),
  then in general (`AlgebraicGeometry.ProEtale.FiniteFor.of_quasiSeparatedSpace`);
- constructibility is local on `Y`
  (`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.of_openCover`), and the higher direct
  images commute with restriction to an open subscheme of `Y`
  (`AlgebraicGeometry.ProEtale.mapDerivedCategoryUpperStarRightDerivedFunctorLowerStarIso`),
  which reduces to an affine target.
-/


@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

section Devissage

variable {l : ℕ} [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

variable (l) in
/-- The objects `K` of the derived category of `ℓ`-adic sheaves on `X_proét` whose derived
pushforward `Rf_* K` is bounded with constructible cohomology sheaves. The finiteness theorem
asserts that it contains every constructible sheaf placed in degree `0`. -/
def finiteLowerStar : ObjectProperty (DerivedCategory (AdicSheaf l X)) :=
  (DerivedCategory.TStructure.t.bounded ⊓
    _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l Y)).inverseImage
      (f)_*ᵃ[l].rightDerivedFunctor

instance : (finiteLowerStar l f).IsClosedUnderIsomorphisms := by
  dsimp [finiteLowerStar]
  infer_instance

/-- **Dévissage for the finiteness theorem**: on a locally noetherian target, the objects with
bounded constructible derived pushforward form a triangulated subcategory, constructible
sheaves being a Serre subcategory and `Rf_*` a triangulated functor. -/
instance [IsLocallyNoetherian Y] : (finiteLowerStar l f).IsTriangulated := by
  have : (DerivedCategory.TStructure.t.bounded ⊓
      _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l Y)).IsTriangulated :=
    inferInstance
  exact inferInstanceAs (ObjectProperty.IsTriangulated (ObjectProperty.inverseImage _
    (f)_*ᵃ[l].rightDerivedFunctor))

/-- **Two out of three for the finiteness theorem**: in a short exact sequence of `ℓ`-adic
sheaves on a scheme over a locally noetherian base, if the outer terms have bounded
constructible derived pushforward then so has the middle one. -/
lemma finiteLowerStar_X₂_of_shortExact [IsLocallyNoetherian Y] {S : ShortComplex (AdicSheaf l X)}
    (hS : S.ShortExact) (h₁ : finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj S.X₁))
    (h₃ : finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj S.X₃)) :
    finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj S.X₂) :=
  (finiteLowerStar l f).ext_of_isTriangulatedClosed₂ _ hS.singleTriangle_distinguished h₁ h₃

/-- **Two out of three for the finiteness theorem**, kernel form. -/
lemma finiteLowerStar_X₁_of_shortExact [IsLocallyNoetherian Y] {S : ShortComplex (AdicSheaf l X)}
    (hS : S.ShortExact) (h₂ : finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj S.X₂))
    (h₃ : finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj S.X₃)) :
    finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj S.X₁) :=
  (finiteLowerStar l f).ext_of_isTriangulatedClosed₁ _ hS.singleTriangle_distinguished h₂ h₃

/-- **Two out of three for the finiteness theorem**, cokernel form. -/
lemma finiteLowerStar_X₃_of_shortExact [IsLocallyNoetherian Y] {S : ShortComplex (AdicSheaf l X)}
    (hS : S.ShortExact) (h₁ : finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj S.X₁))
    (h₂ : finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj S.X₂)) :
    finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj S.X₃) :=
  (finiteLowerStar l f).ext_of_isTriangulatedClosed₃ _ hS.singleTriangle_distinguished h₁ h₂

/-- The finiteness theorem extends from constructible sheaves to bounded complexes with
constructible cohomology sheaves (dévissage along the truncation triangles). -/
lemma finiteLowerStar_of_bounded [IsLocallyNoetherian Y]
    (h : ∀ F : AdicSheaf l X, IsAdicConstructibleSheaf F →
      finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj F))
    (K : DerivedCategory (AdicSheaf l X)) (hK : DerivedCategory.TStructure.t.bounded K)
    (hK' : _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l X) K) :
    finiteLowerStar l f K :=
  DerivedCategory.prop_of_bounded _ (adicConstructibleSheaf l X) h K hK hK'

instance {Z W : Scheme.{u}} (g : Z ⟶ W) : (g)_*ᵃ[l].PreservesKInjectiveComplexes :=
  (adicUpperStarLowerStarAdjunction l g).preservesKInjectiveComplexes

/-- Transport of the finiteness property along an isomorphism of derived pushforwards. -/
lemma finiteLowerStar_of_iso {X' : Scheme.{u}} {g : X' ⟶ Y} {K : DerivedCategory (AdicSheaf l X)}
    {K' : DerivedCategory (AdicSheaf l X')}
    (e : (f)_*ᵃ[l].rightDerivedFunctor.obj K ≅ (g)_*ᵃ[l].rightDerivedFunctor.obj K')
    (h : finiteLowerStar l g K') : finiteLowerStar l f K :=
  ObjectProperty.prop_of_iso (DerivedCategory.TStructure.t.bounded ⊓
    _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l Y)) e.symm h

variable (l) in
/-- For an open immersion `j : Z ⟶ X` and a K-injective complex `I` on `X`,
`Rf_* (j_* j^* I) ≅ R(j ≫ f)_* (j^* I)`. -/
noncomputable def rightDerivedFunctorLowerStarObjQIso {Z : Scheme.{u}} (j : Z ⟶ X)
    [IsOpenImmersion j] (I : CochainComplex (AdicSheaf l X) ℤ) [I.IsKInjective] :
    (f)_*ᵃ[l].rightDerivedFunctor.obj (DerivedCategory.Q.obj
        (((j)_*ᵃ[l].mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((j)^*ᵃ[l].mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) ≅
      (j ≫ f)_*ᵃ[l].rightDerivedFunctor.obj
        ((j)^*ᵃ[l].mapDerivedCategory.obj (DerivedCategory.Q.obj I)) :=
  (f)_*ᵃ[l].rightDerivedFunctor.mapIso ((j)_*ᵃ[l].rightDerivedFunctorObjQIso _).symm ≪≫
    (Functor.rightDerivedFunctorCompIso' (j)_*ᵃ[l] (f)_*ᵃ[l] (adicLowerStarComp l j f)).app _ ≪≫
    (j ≫ f)_*ᵃ[l].rightDerivedFunctor.mapIso (((j)^*ᵃ[l].mapDerivedCategoryFactors).app I).symm

/-- **Mayer–Vietoris for the finiteness theorem** (the Čech step of `sk-prop-sf-finiteness`):
let `X = U ∪ V` be an open cover. An object `K` of the derived category of `ℓ`-adic sheaves on
`X` has bounded constructible derived pushforward along `f` as soon as its restrictions to
`U`, `V` and `U ∩ V` have, along the restrictions of `f`.

The unit `K ⟶ Rj_{U*} K|_U` has a cone `C` vanishing on `U`, hence `C ≅ Rj_{V*} C|_V`
(`AlgebraicGeometry.ProEtale.isIso_Q_map_unit_of_isZero`); restricting the triangle to `V`
and computing `(Rj_{U*} K|_U)|_V` on `U ∩ V` by open base change, `C|_V` sits in a triangle
with `K|_V` and the pushforward of `K|_{U ∩ V}`. -/
theorem finiteLowerStar_of_openCover [IsLocallyNoetherian Y] {U V : Scheme.{u}} (jU : U ⟶ X)
    (jV : V ⟶ X) [IsOpenImmersion jU] [IsOpenImmersion jV]
    (hcov : ∀ x, x ∈ Set.range jU.base ∨ x ∈ Set.range jV.base) {W : Scheme.{u}}
    (pU : W ⟶ U) (pV : W ⟶ V) [IsOpenImmersion pU] (hsq : IsPullback pU pV jU jV)
    (K : DerivedCategory (AdicSheaf l X))
    (hU : finiteLowerStar l (jU ≫ f) ((jU)^*ᵃ[l].mapDerivedCategory.obj K))
    (hV : finiteLowerStar l (jV ≫ f) ((jV)^*ᵃ[l].mapDerivedCategory.obj K))
    (hW : finiteLowerStar l (pV ≫ jV ≫ f)
      ((pU)^*ᵃ[l].mapDerivedCategory.obj ((jU)^*ᵃ[l].mapDerivedCategory.obj K))) :
    finiteLowerStar l f K := by
  obtain ⟨I, _, ⟨eK⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  refine (finiteLowerStar l f).prop_of_iso eK.symm ?_
  obtain ⟨C, v, w, hT⟩ := Pretriangulated.distinguished_cocone_triangle
    (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (adicUpperStarLowerStarAdjunction l jU).unit (ComplexShape.up ℤ)).app I))
  -- the pushforward of `K|_U`
  have h₂ : finiteLowerStar l f (DerivedCategory.Q.obj
      (((jU)_*ᵃ[l].mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((jU)^*ᵃ[l].mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :=
    finiteLowerStar_of_iso f (rightDerivedFunctorLowerStarObjQIso l f jU I)
      ((finiteLowerStar l (jU ≫ f)).prop_of_iso
        ((jU)^*ᵃ[l].mapDerivedCategory.mapIso eK) hU)
  -- the cone vanishes on `U`
  have hCU : IsZero ((jU)^*ᵃ[l].mapDerivedCategory.obj C) :=
    Pretriangulated.Triangle.isZero₃_of_isIso₁ _
      ((jU)^*ᵃ[l].mapDerivedCategory.map_distinguished _ hT)
      (isIso_mapDerivedCategory_Q_map_unit l jU I)
  -- hence the cone is pushed forward from `V`
  obtain ⟨J, _, ⟨eC⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective C
  have hJ := isIso_Q_map_unit_of_isZero l jU jV hcov J
    (hCU.of_iso ((jU)^*ᵃ[l].mapDerivedCategory.mapIso eC.symm))
  -- the restriction of the triangle to `V`
  have hTV := (jV)^*ᵃ[l].mapDerivedCategory.map_distinguished _ hT
  let J₀ := ((jU)^*ᵃ[l].mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have h₁V : finiteLowerStar l (jV ≫ f) ((jV)^*ᵃ[l].mapDerivedCategory.obj
      (DerivedCategory.Q.obj I)) :=
    (finiteLowerStar l (jV ≫ f)).prop_of_iso ((jV)^*ᵃ[l].mapDerivedCategory.mapIso eK) hV
  have h₂V : finiteLowerStar l (jV ≫ f) ((jV)^*ᵃ[l].mapDerivedCategory.obj
      (DerivedCategory.Q.obj (((jU)_*ᵃ[l].mapHomologicalComplex (ComplexShape.up ℤ)).obj J₀))) :=
    finiteLowerStar_of_iso (jV ≫ f)
      ((jV ≫ f)_*ᵃ[l].rightDerivedFunctor.mapIso
          ((jV)^*ᵃ[l].mapDerivedCategory.mapIso ((jU)_*ᵃ[l].rightDerivedFunctorObjQIso J₀).symm ≪≫
            (adicDerivedBaseChangeIso l hsq.flip).app _) ≪≫
        (Functor.rightDerivedFunctorCompIso' (pV)_*ᵃ[l] (jV ≫ f)_*ᵃ[l]
          (adicLowerStarComp l pV (jV ≫ f))).app _)
      ((finiteLowerStar l (pV ≫ jV ≫ f)).prop_of_iso
        ((pU)^*ᵃ[l].mapDerivedCategory.mapIso
          ((jU)^*ᵃ[l].mapDerivedCategory.mapIso eK ≪≫
            ((jU)^*ᵃ[l].mapDerivedCategoryFactors).app I)) hW)
  have h₃V : finiteLowerStar l (jV ≫ f) ((jV)^*ᵃ[l].mapDerivedCategory.obj C) :=
    (finiteLowerStar l (jV ≫ f)).ext_of_isTriangulatedClosed₃ _ hTV h₁V h₂V
  have h₃ : finiteLowerStar l f C :=
    finiteLowerStar_of_iso f
      ((f)_*ᵃ[l].rightDerivedFunctor.mapIso (eC ≪≫ asIso (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (adicUpperStarLowerStarAdjunction l jV).unit
            (ComplexShape.up ℤ)).app J))) ≪≫
        rightDerivedFunctorLowerStarObjQIso l f jV J ≪≫
        (jV ≫ f)_*ᵃ[l].rightDerivedFunctor.mapIso
          ((jV)^*ᵃ[l].mapDerivedCategory.mapIso eC.symm)) h₃V
  exact (finiteLowerStar l f).ext_of_isTriangulatedClosed₁ _ hT h₂ h₃

end Devissage

section CoverInduction

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}

variable (l) in
/-- The finiteness theorem for `g : T ⟶ Y`: every bounded complex of `ℓ`-adic sheaves on `T` with
constructible cohomology sheaves has bounded constructible derived pushforward along `g`. -/
def FiniteFor {T : Scheme.{u}} (g : T ⟶ Y) : Prop :=
  ∀ K : DerivedCategory (AdicSheaf l T), DerivedCategory.TStructure.t.bounded K →
    _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l T) K →
      finiteLowerStar l g K

/-- The restriction of a bounded complex with constructible cohomology is again one. -/
lemma bounded_homologyProperty_mapDerivedCategory_adicUpperStar {T T' : Scheme.{u}}
    (j : T' ⟶ T) {K : DerivedCategory (AdicSheaf l T)}
    (hb : DerivedCategory.TStructure.t.bounded K)
    (hc : _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l T) K) :
    DerivedCategory.TStructure.t.bounded ((j)^*ᵃ[l].mapDerivedCategory.obj K) ∧
      _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l T')
        ((j)^*ᵃ[l].mapDerivedCategory.obj K) :=
  ⟨(j)^*ᵃ[l].bounded_mapDerivedCategory_obj hb, fun n ↦
    ((hc n).upperStar j).of_iso (((j)^*ᵃ[l].mapDerivedCategoryHomologyFunctorIso n).app K)⟩

/-- **Mayer–Vietoris for open subschemes**: the finiteness theorem for the restrictions of `g`
to two opens and to their intersection gives it on their union. -/
lemma FiniteFor.sup [IsLocallyNoetherian Y] {T : Scheme.{u}} (g : T ⟶ Y) (O₁ O₂ : T.Opens)
    (h₁ : FiniteFor l (O₁.ι ≫ g)) (h₂ : FiniteFor l (O₂.ι ≫ g))
    (h₁₂ : FiniteFor l ((O₁ ⊓ O₂).ι ≫ g)) : FiniteFor l ((O₁ ⊔ O₂).ι ≫ g) := by
  intro K hb hc
  refine finiteLowerStar_of_openCover ((O₁ ⊔ O₂).ι ≫ g) (T.homOfLE le_sup_left)
    (T.homOfLE le_sup_right) (fun x ↦ ?_) (T.homOfLE inf_le_left) (T.homOfLE inf_le_right)
    (isPullback_opens_inf_le le_sup_left le_sup_right) K ?_ ?_ ?_
  · obtain ⟨y, hy⟩ := x
    rcases TopologicalSpace.Opens.mem_sup.1 hy with h | h
    · exact Or.inl ⟨⟨y, h⟩, Scheme.homOfLE_apply' _ _ _⟩
    · exact Or.inr ⟨⟨y, h⟩, Scheme.homOfLE_apply' _ _ _⟩
  · have := bounded_homologyProperty_mapDerivedCategory_adicUpperStar (l := l)
      (T.homOfLE (le_sup_left : O₁ ≤ O₁ ⊔ O₂)) hb hc
    rw [Scheme.homOfLE_ι_assoc]
    exact h₁ _ this.1 this.2
  · have := bounded_homologyProperty_mapDerivedCategory_adicUpperStar (l := l)
      (T.homOfLE (le_sup_right : O₂ ≤ O₁ ⊔ O₂)) hb hc
    rw [Scheme.homOfLE_ι_assoc]
    exact h₂ _ this.1 this.2
  · have h := bounded_homologyProperty_mapDerivedCategory_adicUpperStar (l := l)
      (T.homOfLE (inf_le_left : O₁ ⊓ O₂ ≤ O₁))
      (bounded_homologyProperty_mapDerivedCategory_adicUpperStar (l := l)
        (T.homOfLE (le_sup_left : O₁ ≤ O₁ ⊔ O₂)) hb hc).1
      (bounded_homologyProperty_mapDerivedCategory_adicUpperStar (l := l)
        (T.homOfLE (le_sup_left : O₁ ≤ O₁ ⊔ O₂)) hb hc).2
    rw [Scheme.homOfLE_homOfLE_assoc, Scheme.homOfLE_ι_assoc]
    exact h₁₂ _ h.1 h.2

open ZeroObject in
variable (l) in
/-- On an empty scheme every object of the derived category of `ℓ`-adic sheaves vanishes: the
empty family covers it, so restrictions along it are jointly conservative. -/
lemma isZero_of_isEmpty {T : Scheme.{u}} [IsEmpty T] (K : DerivedCategory (AdicSheaf l T)) :
    IsZero K := by
  have : IsIso (0 : K ⟶ 0) := isIso_of_isIso_mapDerivedCategory_adicUpperStar l
    (W := (Empty.elim : Empty → Scheme.{u})) (fun i ↦ i.elim) (by
      exact Scheme.zariskiPrecoverage_le_proetalePrecoverage _
        ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun x ↦ isEmptyElim x, fun i ↦ i.elim⟩))
    _ (fun i ↦ i.elim)
  exact (isZero_zero _).of_iso (asIso (0 : K ⟶ 0))

/-- The finiteness theorem holds trivially over an empty source. -/
lemma FiniteFor.of_isEmpty [IsLocallyNoetherian Y] {T : Scheme.{u}} [IsEmpty T] (g : T ⟶ Y) :
    FiniteFor l g := fun K _ _ ↦
  (finiteLowerStar l g).prop_of_isZero (isZero_of_isEmpty l K)

lemma FiniteFor.congr_opens {T : Scheme.{u}} (g : T ⟶ Y) {O O' : T.Opens} (h : O = O')
    (hO : FiniteFor l (O.ι ≫ g)) : FiniteFor l (O'.ι ≫ g) := by
  subst h
  exact hO

/-- The finiteness theorem for the restriction of `g` to the open subscheme `⊤` gives it for
`g`. -/
lemma FiniteFor.of_top [IsLocallyNoetherian Y] {T : Scheme.{u}} (g : T ⟶ Y)
    (h : FiniteFor l ((⊤ : T.Opens).ι ≫ g)) : FiniteFor l g := by
  intro K hb hc
  have h₁ := bounded_homologyProperty_mapDerivedCategory_adicUpperStar (l := l)
    (⊤ : T.Opens).ι hb hc
  have h₂ := bounded_homologyProperty_mapDerivedCategory_adicUpperStar (l := l)
    (T.homOfLE (inf_le_left : (⊤ : T.Opens) ⊓ ⊤ ≤ ⊤)) h₁.1 h₁.2
  refine finiteLowerStar_of_openCover g (⊤ : T.Opens).ι (⊤ : T.Opens).ι
    (fun x ↦ Or.inl (by rw [Scheme.Opens.range_ι]; trivial)) (T.homOfLE inf_le_left)
    (T.homOfLE inf_le_right) (isPullback_opens_inf ⊤ ⊤) K (h _ h₁.1 h₁.2) (h _ h₁.1 h₁.2) ?_
  rw [Scheme.homOfLE_ι_assoc]
  exact FiniteFor.congr_opens g (inf_idem ⊤).symm h _ h₂.1 h₂.2

/-- **Finite unions**: for a class `P` of opens closed under binary intersections, on which the
finiteness theorem holds, it holds on every finite union of members of `P`. -/
lemma FiniteFor.finsetSup [IsLocallyNoetherian Y] {T : Scheme.{u}} (g : T ⟶ Y)
    (P : T.Opens → Prop) (hP : ∀ O O', P O → P O' → P (O ⊓ O'))
    (h : ∀ O, P O → FiniteFor l (O.ι ≫ g)) (S : Finset T.Opens) (hS : ∀ O ∈ S, P O) :
    FiniteFor l ((S.sup id).ι ≫ g) := by
  classical
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
  rcases S.eq_empty_or_nonempty with rfl | ⟨U, hU⟩
  · have : IsEmpty ((Finset.sup ∅ id : T.Opens) : Scheme.{u}) := ⟨fun x ↦ x.2⟩
    exact FiniteFor.of_isEmpty _
  have hS' : S.sup id = U ⊔ (S.erase U).sup id :=
    (congrArg (fun S' ↦ Finset.sup S' id) (Finset.insert_erase hU)).symm.trans Finset.sup_insert
  have hlt : (S.erase U).card < n := hn ▸ Finset.card_erase_lt_of_mem hU
  refine FiniteFor.congr_opens g hS'.symm
    (FiniteFor.sup g U ((S.erase U).sup id) (h U (hS U hU))
      (ih _ hlt _ (fun O hO ↦ hS O (Finset.mem_of_mem_erase hO)) rfl) ?_)
  refine FiniteFor.congr_opens g (by rw [Finset.sup_inf_distrib_left, Finset.sup_image]; rfl)
    (ih _ (lt_of_le_of_lt Finset.card_image_le hlt) ((S.erase U).image (U ⊓ ·)) ?_ rfl)
  simp only [Finset.mem_image, Finset.mem_erase]
  rintro _ ⟨O, ⟨-, hO⟩, rfl⟩
  exact hP _ _ (hS U hU) (hS O hO)

/-- **The separated case**: on a quasi-compact scheme with affine diagonal, the finiteness
theorem follows from the case of its affine opens, these being stable under intersections. -/
lemma FiniteFor.of_isAffineHom_diagonal [IsLocallyNoetherian Y] {T : Scheme.{u}} (g : T ⟶ Y)
    [CompactSpace T] [IsAffineHom (pullback.diagonal (terminal.from T))]
    (h : ∀ O : T.Opens, IsAffineOpen O → FiniteFor l (O.ι ≫ g)) : FiniteFor l g := by
  obtain ⟨S, hSa, hS⟩ := Scheme.exists_finset_isAffineOpen_sup_eq_top T
  exact FiniteFor.of_top g (FiniteFor.congr_opens g hS
    (FiniteFor.finsetSup g IsAffineOpen (fun _ _ hO hO' ↦ hO.inf hO') h S hSa))

/-- **The quasi-separated case**: on a quasi-compact quasi-separated scheme, the finiteness
theorem follows from the case of affine schemes. The quasi-compact opens contained in an affine
open are stable under intersections, and have affine diagonal, so the separated case applies to
them. -/
lemma FiniteFor.of_quasiSeparatedSpace [IsLocallyNoetherian Y] {T : Scheme.{u}} (g : T ⟶ Y)
    [CompactSpace T] [QuasiSeparatedSpace T] [LocallyOfFiniteType g]
    (h : ∀ (T' : Scheme.{u}) [IsAffine T'] (g' : T' ⟶ Y) [LocallyOfFiniteType g'],
      FiniteFor l g') : FiniteFor l g := by
  let P : T.Opens → Prop := fun O ↦ IsCompact (O : Set T) ∧ ∃ U, IsAffineOpen U ∧ O ≤ U
  have hP : ∀ O O', P O → P O' → P (O ⊓ O') := fun O O' ⟨hO, U, hU, hOU⟩ ⟨hO', _⟩ ↦
    ⟨QuasiSeparatedSpace.inter_isCompact _ _ O.isOpen hO O'.isOpen hO',
      U, hU, inf_le_left.trans hOU⟩
  have hPF : ∀ O, P O → FiniteFor l (O.ι ≫ g) := by
    rintro O ⟨hO, U, hU, hOU⟩
    have : CompactSpace O.toScheme := isCompact_iff_compactSpace.1 hO
    have : IsAffine U.toScheme := hU
    have : IsSeparated (terminal.from O.toScheme) := by
      rw [show terminal.from O.toScheme = T.homOfLE hOU ≫ terminal.from U.toScheme from
        terminal.hom_ext _ _]
      infer_instance
    refine FiniteFor.of_isAffineHom_diagonal (O.ι ≫ g) fun O' hO' ↦ ?_
    have : IsAffine O'.toScheme := hO'
    exact h O'.toScheme (O'.ι ≫ O.ι ≫ g)
  obtain ⟨S, hSa, hS⟩ := Scheme.exists_finset_isAffineOpen_sup_eq_top T
  exact FiniteFor.of_top g (FiniteFor.congr_opens g hS
    (FiniteFor.finsetSup g P hP hPF S fun O hO ↦ ⟨(hSa O hO).isCompact, O, hSa O hO, le_rfl⟩))

end CoverInduction

section Finiteness

variable {l : ℕ} [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A constructible sheaf placed in degree `0` is bounded with constructible cohomology. -/
lemma bounded_homologyProperty_singleFunctor {T : Scheme.{u}} {F : AdicSheaf l T}
    (hF : IsAdicConstructibleSheaf F) :
    DerivedCategory.TStructure.t.bounded ((DerivedCategory.singleFunctor _ 0).obj F) ∧
      _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l T)
        ((DerivedCategory.singleFunctor _ 0).obj F) := by
  refine ⟨⟨⟨0, inferInstanceAs (DerivedCategory.IsGE
      ((DerivedCategory.singleFunctor _ 0).obj F) 0)⟩,
    ⟨0, inferInstanceAs (DerivedCategory.IsLE
      ((DerivedCategory.singleFunctor _ 0).obj F) 0)⟩⟩, fun m ↦ ?_⟩
  obtain hm | rfl | hm := lt_trichotomy m 0
  · exact (adicConstructibleSheaf l T).prop_of_isZero
      ((DerivedCategory.isGE_iff ((DerivedCategory.singleFunctor _ 0).obj F) 0).1
        inferInstance m hm)
  · exact (adicConstructibleSheaf l T).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm hF
  · exact (adicConstructibleSheaf l T).prop_of_isZero
      ((DerivedCategory.isLE_iff ((DerivedCategory.singleFunctor _ 0).obj F) 0).1
        inferInstance m hm)

/-- **Constructibility is local on the base**: an `ℓ`-adic sheaf whose restrictions to the
members of an open cover are constructible is constructible. -/
lemma IsAdicConstructibleSheaf.of_openCover {G : AdicSheaf l Y}
    (h : ∀ y : Y, ∃ (V : Scheme.{u}) (j : V ⟶ Y), IsOpenImmersion j ∧ y ∈ Set.range j.base ∧
      IsAdicConstructibleSheaf ((j)^*ᵃ[l].obj G)) :
    IsAdicConstructibleSheaf G := by
  intro y
  obtain ⟨V, j, hj, ⟨v, rfl⟩, hG⟩ := h y
  obtain ⟨W, i, hi, ⟨w, rfl⟩, hW⟩ := hG v
  exact ⟨W, i ≫ j, inferInstance, ⟨w, rfl⟩,
    hW.of_iso ((adicUpperStarComp l i j).app G).symm⟩

/-- The restriction of `Rf_* F` to an open subscheme `V` of the target is computed on
`X ×_Y V` by open base change. -/
noncomputable def mapDerivedCategoryUpperStarRightDerivedFunctorLowerStarIso {V : Scheme.{u}}
    (j : V ⟶ Y) [IsOpenImmersion j] (F : AdicSheaf l X) :
    (j)^*ᵃ[l].mapDerivedCategory.obj ((f)_*ᵃ[l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
      (pullback.snd f j)_*ᵃ[l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj ((pullback.fst f j)^*ᵃ[l].obj F)) :=
  (adicDerivedBaseChangeIso l (IsPullback.of_hasPullback f j).flip).app _ ≪≫
    Functor.mapIso _ (((pullback.fst f j)^*ᵃ[l].mapDerivedCategorySingleFunctor 0).app F)

end Finiteness


end AlgebraicGeometry.ProEtale
