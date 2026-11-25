/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalPointFactorization
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.TraceFormula.CurveLocal.CoverPuncturedFactors
public import WeilConjectures.TraceFormula.CurveLocal.ExtensionByZero
public import WeilConjectures.TraceFormula.CurveLocal.TensorMonodromy

/-!

# The complex `E'` on the complement of the axes in `T'`

For a cover datum, the pullback of `P = Lτ^*(L ⊠ K)` to `T' ∖ D'` is the extension by zero of a
complex `E'` on `T' ∖ (D' ∪ H')` with finite `ℓ`-group monodromy (blueprint
`lemma-tangent-cones-on-cover` (i) and `lemma-vanishing-local-term-zero-stalk--1` (i)):

* `P` vanishes on `H'` when `Ly^* K = 0`, since `H'` lies over the horizontal axis;
* on `T' ∖ (D' ∪ H')`, both projections to `C` land in the punctured neighbourhood
  `p⁻¹(W ∖ y)` (`CoverDatum.ψ₁`, `CoverDatum.ψ₂`), so that the restriction of `P` is
  `Lψ₁^* P₁ ⊗ᴸ Lψ₂^* P₂` for the pullbacks `P₁`, `P₂` of the models of `L`, `K`, which are
  trivialized by the Galois cover of the datum.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The derived pullback of a levelwise pullback: `Lg^*(D(h^*) X) ≅ L(gh)^* X` for `gh = g ≫ h`. -/
noncomputable def leftDerivedUpperStarObjMapDerivedCategoryObjIso {S Y Z : Scheme.{u}}
    (g : S ⟶ Y) (h : Y ⟶ Z) (gh : S ⟶ Z) (hgh : gh = g ≫ h)
    (X : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    L((g)^*[ModuleCat.{u + 1} Λ]).obj (D((h)^*[ModuleCat.{u + 1} Λ]).obj X) ≅
      L((gh)^*[ModuleCat.{u + 1} Λ]).obj X :=
  L((g)^*[ModuleCat.{u + 1} Λ]).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ h).app X).symm ≪≫
    ((leftDerivedUpperStarComp _ g h gh hgh).app X).symm

/-- If `g = ψ ≫ r` and `L ≅ Q(P)`, then `Lg^* L ≅ Lψ^*(Q(r^* P))`, with `r^* P` the levelwise
pullback. -/
noncomputable def leftDerivedUpperStarObjIsoOfFactor {S V X : Scheme.{u}} (g : S ⟶ X)
    (ψ : S ⟶ V) (r : V ⟶ X) (h : g = ψ ≫ r)
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
    (eL : L ≅ DerivedCategory.Q.obj P) :
    L((g)^*[ModuleCat.{u + 1} Λ]).obj L ≅
      L((ψ)^*[ModuleCat.{u + 1} Λ]).obj (DerivedCategory.Q.obj
        (((r)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj P)) :=
  (leftDerivedUpperStarComp _ ψ r g h).app L ≪≫
    L((ψ)^*[ModuleCat.{u + 1} Λ]).mapIso
      (L((r)^*[ModuleCat.{u + 1} Λ]).mapIso eL ≪≫ leftDerivedUpperStarObjQObjIso r P)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] {M : CurveLocalModel k} {ℓ : ℕ}
  {Λ : Type (u + 1)} [CommRing Λ]
  {PL PK : CochainComplex (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
  (D : M.CoverDatum ℓ PL PK)

attribute [local instance] CoverDatum.group CoverDatum.finite

/-- The first projection `T' ∖ (D' ∪ H') ⟶ p⁻¹(W ∖ y)`. -/
noncomputable def ψ₁ : D.O'.toScheme ⟶ D.Vc.toScheme :=
  IsOpenImmersion.lift D.Vc.ι (D.O'.ι ≫ strictLocalizationToBase D.s' ≫ pullback.fst D.fC D.fC)
    (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact D.fst_mem_Vc z.1 z.2)

/-- The second projection `T' ∖ (D' ∪ H') ⟶ p⁻¹(W ∖ y)`. -/
noncomputable def ψ₂ : D.O'.toScheme ⟶ D.Vc.toScheme :=
  IsOpenImmersion.lift D.Vc.ι (D.O'.ι ≫ strictLocalizationToBase D.s' ≫ pullback.snd D.fC D.fC)
    (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact D.snd_mem_Vc z.1 z.2)

@[reassoc (attr := simp)]
lemma ψ₁_ι : D.ψ₁ ≫ D.Vc.ι = D.O'.ι ≫ strictLocalizationToBase D.s' ≫ pullback.fst D.fC D.fC :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
lemma ψ₂_ι : D.ψ₂ ≫ D.Vc.ι = D.O'.ι ≫ strictLocalizationToBase D.s' ≫ pullback.snd D.fC D.fC :=
  IsOpenImmersion.lift_fac _ _ _

/-- The open immersion `T' ∖ (D' ∪ H') ⟶ T' ∖ D'`. -/
noncomputable abbrev iO' : D.O'.toScheme ⟶ D.dD'.openComplement.toScheme :=
  D.T'.homOfLE (inf_le_left : D.O' ≤ D.dD'.openComplement)

lemma iO'_fst :
    ((D.iO' ≫ D.dD'.openComplement.ι ≫ D.π) ≫ M.τ) ≫ pullback.fst M.f M.f =
      D.ψ₁ ≫ D.Vc.ι ≫ D.p := by
  simp only [Category.assoc, ψ₁_ι_assoc, Scheme.homOfLE_ι_assoc]
  rw [← Category.assoc D.π, D.π_comp_τ, Category.assoc, D.g_fst]

lemma iO'_snd :
    ((D.iO' ≫ D.dD'.openComplement.ι ≫ D.π) ≫ M.τ) ≫ pullback.snd M.f M.f =
      D.ψ₂ ≫ D.Vc.ι ≫ D.p := by
  simp only [Category.assoc, ψ₂_ι_assoc, Scheme.homOfLE_ι_assoc]
  rw [← Category.assoc D.π, D.π_comp_τ, Category.assoc, D.g_snd]

omit [IsAlgClosed k] in
lemma isClosedImmersion_y (M : CurveLocalModel k) : IsClosedImmersion M.y := by
  have : IsClosedImmersion (M.y ≫ M.f) := by
    rw [M.y_comp]
    infer_instance
  exact IsClosedImmersion.of_comp M.y M.f

/-- A geometric point of `T' ∖ D'` outside `T' ∖ (D' ∪ H')` lies on `H'`, hence its second
coordinate factors through `y`. -/
lemma comp_snd_eq_of_not_mem_range {Ω : Type u} [Field Ω]
    (s : Spec (.of Ω) ⟶ D.dD'.openComplement.toScheme)
    (hs : s.base (IsLocalRing.closedPoint Ω) ∉ Set.range D.iO'.base) :
    ((s ≫ D.dD'.openComplement.ι ≫ D.π) ≫ M.τ) ≫ pullback.snd M.f M.f =
      ((((s ≫ D.dD'.openComplement.ι ≫ D.π) ≫ M.τ) ≫ pullback.snd M.f M.f) ≫ M.f) ≫ M.y := by
  have := isClosedImmersion_y M
  refine Scheme.eq_comp_of_apply_eq M.f M.y M.y_comp _ ?_
  set x := s.base (IsLocalRing.closedPoint Ω)
  have hx : x.1 ∉ D.dH'.openComplement := fun h ↦
    hs ⟨⟨x.1, ⟨x.2, h⟩⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  have hx' : x.1 ∈ Set.range D.dH'.base := not_not.1 hx
  rw [range_reducedClosedι, (D.isClosed_preimage_range M.hH).closure_eq, Set.mem_preimage,
    mem_range_hH_iff] at hx'
  simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
  rw [hx']
  exact congrArg _ (Subsingleton.elim _ _)

variable (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
  (P : DerivedCategory (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

/-- The derived pullback of `P|_{T' ∖ D'}` along `g : S ⟶ T' ∖ D'` is the derived pullback of
`L ⊠ K` along the composite `S ⟶ T' ⟶ T ⟶ X ×_k X`. -/
noncomputable def leftDerivedUpperStarRestrictionIso {S : Scheme.{u}}
    (g : S ⟶ D.dD'.openComplement.toScheme)
    (eP : P ≅ (L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)) :
    L((g)^*[ModuleCat.{u + 1} Λ]).obj ((D.dD'.openComplement.ι)^*[ModuleCat.{u + 1} Λ]
        |>.mapDerivedCategory.obj ((D.π)^*[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj P)) ≅
      L((((g ≫ D.dD'.openComplement.ι ≫ D.π) ≫ M.τ))^*[ModuleCat.{u + 1} Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K) :=
  leftDerivedUpperStarObjMapDerivedCategoryObjIso g _ _ rfl _ ≪≫
    leftDerivedUpperStarObjMapDerivedCategoryObjIso _ D.π (g ≫ D.dD'.openComplement.ι ≫ D.π)
      (Category.assoc _ _ _).symm P ≪≫
    L((g ≫ D.dD'.openComplement.ι ≫ D.π)^*[ModuleCat.{u + 1} Λ]).mapIso eP ≪≫
    ((leftDerivedUpperStarComp _ _ M.τ).app _).symm

/-- `P` vanishes at the geometric points of `T' ∖ D'` outside `T' ∖ (D' ∪ H')` when
`Ly^* K = 0`. -/
lemma isZero_leftDerivedUpperStar_restriction_of_not_mem_range
    (hKy : IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K))
    (eP : P ≅ (L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K))
    {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ D.dD'.openComplement.toScheme)
    (hs : s.base (IsLocalRing.closedPoint Ω) ∉ Set.range D.iO'.base) :
    IsZero (L((s)^*[ModuleCat.{u + 1} Λ]).obj ((D.dD'.openComplement.ι)^*[ModuleCat.{u + 1} Λ]
        |>.mapDerivedCategory.obj ((D.π)^*[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj P))) :=
  (M.isZero_leftDerivedUpperStar_externalProduct_of_comp_snd_eq _ _
    (D.comp_snd_eq_of_not_mem_range s hs) L K hKy).of_iso
    (D.leftDerivedUpperStarRestrictionIso L K P s eP)

/-- `P|_{T' ∖ D'}` is the extension by zero of its restriction to `T' ∖ (D' ∪ H')` when
`Ly^* K = 0` (blueprint `lemma-vanishing-local-term-zero-stalk--1` (i)). -/
lemma isIso_counit_app_restriction
    (hKy : IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K))
    (eP : P ≅ (L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)) :
    IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
      D.iO').counit.app ((D.dD'.openComplement.ι)^*[ModuleCat.{u + 1} Λ]
        |>.mapDerivedCategory.obj ((D.π)^*[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj P))) :=
  isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_counit_app_of_forall _ _
    fun _ _ _ s hs ↦ D.isZero_leftDerivedUpperStar_restriction_of_not_mem_range L K P hKy eP s hs

/-- The pullback of the model `PL` to the punctured neighbourhood `p⁻¹(W ∖ y)`. -/
noncomputable abbrev P₁ : CochainComplex (Sheaf D.Vc.toScheme.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) ℤ :=
  ((D.Vc.ι ≫ D.p)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj PL

/-- The pullback of the model `PK` to the punctured neighbourhood `p⁻¹(W ∖ y)`. -/
noncomputable abbrev P₂ : CochainComplex (Sheaf D.Vc.toScheme.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) ℤ :=
  ((D.Vc.ι ≫ D.p)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj PK

/-- The restriction of `P` to `T' ∖ (D' ∪ H')` is `Lψ₁^* P₁ ⊗ᴸ Lψ₂^* P₂`. -/
noncomputable def restrictionIso
    (eL : L ≅ DerivedCategory.Q.obj PL) (eK : K ≅ DerivedCategory.Q.obj PK)
    (eP : P ≅ (L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)) :
    (D.iO')^*[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj
        ((D.dD'.openComplement.ι)^*[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj
          ((D.π)^*[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj P)) ≅
      ((-⊗ᴸ-(D.O'.toScheme)[ModuleCat.{u + 1} Λ]).obj
        (L((D.ψ₁)^*[ModuleCat.{u + 1} Λ]).obj (DerivedCategory.Q.obj D.P₁))).obj
          (L((D.ψ₂)^*[ModuleCat.{u + 1} Λ]).obj (DerivedCategory.Q.obj D.P₂)) :=
  ((leftDerivedUpperStarIsoMapDerivedCategory _ D.iO').app _).symm ≪≫
    D.leftDerivedUpperStarRestrictionIso L K P D.iO' eP ≪≫
    leftDerivedUpperStarTensorIso _ _ _ _ ≪≫
    ((derivedTensor _ _).mapIso
      (((leftDerivedUpperStarComp _ _ (pullback.fst M.f M.f)).app L).symm ≪≫
        leftDerivedUpperStarObjIsoOfFactor _ D.ψ₁ (D.Vc.ι ≫ D.p) D.iO'_fst eL)).app _ ≪≫
    ((derivedTensor _ _).obj _).mapIso
      (((leftDerivedUpperStarComp _ _ (pullback.snd M.f M.f)).app K).symm ≪≫
        leftDerivedUpperStarObjIsoOfFactor _ D.ψ₂ (D.Vc.ι ≫ D.p) D.iO'_snd eK)

omit [IsAlgClosed k] in
/-- The termwise pullback of a model to the Galois cover of the datum is constant. -/
lemma exists_galois_trivializes (Q : CochainComplex (Sheaf M.X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) ℤ) (hQ : Q ∈ ({PL, PK} : Set _)) :
    ∃ (C : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) (a b : ℤ) (_ : C.IsStrictlyGE a)
      (_ : C.IsStrictlyLE b) (_ : ∀ n, Finite (C.X n)),
      Nonempty (((D.galois.π)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj
          (((D.Vc.ι ≫ D.p)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj Q) ≅
        ((constantSheaf D.galois.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
          (.up ℤ)).obj C) := by
  obtain ⟨C, a, b, h₁, h₂, h₃, ⟨e⟩⟩ := D.trivializes Q hQ
  exact ⟨C, a, b, h₁, h₂, h₃,
    ⟨upperStarMapHomologicalComplexConstantIso (𝟙 _) D.galois.π (Category.id_comp _).symm e⟩⟩

/-- **The complex `E'`** (blueprint `lemma-tangent-cones-on-cover` (i),
`lemma-vanishing-local-term-zero-stalk--1` (i)): if `Ly^* K = 0`, the pullback of `P` to `T' ∖ D'`
is the extension by zero of a bounded complex `E'` on `T' ∖ (D' ∪ H')` with finite `ℓ`-group
monodromy. -/
theorem exists_complexE [Finite Λ]
    (hKy : IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K))
    (hPL : ∃ a b, IsBoundedFlatComplex Λ a b PL) (hPK : ∃ a b, IsBoundedFlatComplex Λ a b PK)
    (eL : L ≅ DerivedCategory.Q.obj PL) (eK : K ≅ DerivedCategory.Q.obj PK)
    (eP : P ≅ (L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)) :
    ∃ (E' : DerivedCategory (Sheaf
        (D.dD'.openComplement ⊓ D.dH'.openComplement).toScheme.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)))
      (_ : (∃ a b : ℤ, E'.IsGE a ∧ E'.IsLE b) ∧ ∀ n : ℤ,
        ∃ (G : Type (u + 1)) (_ : Group G) (_ : Finite G) (_ : IsPGroup ℓ G)
          (c : Scheme.GaloisCover G (D.dD'.openComplement ⊓ D.dH'.openComplement).toScheme)
          (N : ModuleCat.{u + 1} Λ) (_ : Finite N),
          Nonempty ((c.π)^*[ModuleCat.{u + 1} Λ].obj
              ((DerivedCategory.homologyFunctor _ n).obj E') ≅
            (constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N)),
      Nonempty ((D.dD'.openComplement.ι)^*[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj
          ((D.π)^*[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj P) ≅
        ((strictLocalization D.s').homOfLE (inf_le_left : D.dD'.openComplement ⊓
          D.dH'.openComplement ≤ D.dD'.openComplement))_!open[ModuleCat.{u + 1} Λ]
            |>.mapDerivedCategory.obj E') := by
  obtain ⟨a₁, b₁, hPL⟩ := hPL
  obtain ⟨a₂, b₂, hPK⟩ := hPK
  have := D.isIso_counit_app_restriction L K P hKy eP
  exact ⟨_, exists_galoisCover_homology_derivedTensor_iso_constantSheaf ℓ D.ψ₁ D.ψ₂
    (isBoundedFlatComplex_upperStar _ hPL) (isBoundedFlatComplex_upperStar _ hPK) D.isPGroup
    D.isPGroup D.galois D.galois (D.exists_galois_trivializes PL (by simp))
    (D.exists_galois_trivializes PK (by simp)) _ (D.restrictionIso L K P eL eK eP),
    ⟨(asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction _ D.iO').counit.app _)).symm⟩⟩

end AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum
