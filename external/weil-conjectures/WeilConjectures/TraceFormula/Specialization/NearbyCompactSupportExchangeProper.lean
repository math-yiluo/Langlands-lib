/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyCompactSupportExchange

/-!

# The compact-support exchange of a proper trait model

For a trait model `N` over the base of a proper `k`-scheme `Y` with proper special fibre, the
compact-support exchange `ν_a : Ra'_! Ψ_N ⟶ Ψ_S Ra_!` of a compactification is the inverse of the
proper exchange `χ_a` under `Ra_! ≅ Ra_*` and `Ra'_! ≅ Ra'_*`
(`Compactification.compactSupportExchange_app_comp_map_comp_pushforwardExchange_app`).

## Proof

The open immersion `ι : Y ⟶ X` of the compactification is also proper, so the canonical map
`e : ι_! ≅ Rι_! ≅ Rι_*` has an adjoint `Lι^* ι_! ⟶ 𝟭` left inverse to the unit
(`ProEtale.CondensedRing.openImmersionAdjunction_unit_app_comp_map_comp_counit_app`). This gives
the degenerate refinement identity `ν_ι ≫ Ψ_P(e) ≫ χ_φ = e'`
(`ProEtale.CondensedRing.lowerShriekExchangeOfInv_app_comp_map_comp_app_eq_of_unit`), and `e`
is compatible with `Ra_! ≅ ι_! ⋙ Ra_{1*}` and `Ra_! ≅ Ra_*`
(`compactificationLowerShriekIso_hom_app_comp_map_comp_lowerStarCompOfEq_hom_app`).
With the composition law `χ_a = Ra'_{1*}(χ_φ) ∘ χ_{a₁}(Rι_*)` of the proper exchanges, the
assembly is the formal `ProEtale.CondensedRing.compactSupportExchangeAux_lift_app_hom_comp_eq`,
instantiated in
`compactSupportExchangeOfCompactification_app_comp_map_comp_pushforwardExchange_app`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Abstract

variable {DN DN' D₁ D₁' : Type*} [Category DN] [Category DN'] [Category D₁] [Category D₁']

/-- **The key identity of a degenerate refinement**, in abstract categories: let `Dh₁ ⊣ Lπ`
(and `Dh₁' ⊣ Lπ'`) be the open adjunctions of an open and proper `ι`, `Lπ ⊣ Rπ` (and
`Lπ' ⊣ Rπ'`) the adjunctions of `ι`, `α` an invertible pullback exchange and `χπ` its mate
(`hχπ`). If `e : Dh₁ K ⟶ Rπ K` and `e' : Dh₁' Ψ_N K ⟶ Rπ' Ψ_N K` have adjoints
`Lπ(e) ≫ ε` and `Lπ'(e') ≫ ε'` left inverse to the units (`hE`, `hE'`), the second unit being
invertible, then the mate `ν` of `α⁻¹` satisfies `ν_K ≫ Ψ₁(e) ≫ χπ_K = e'`. -/
lemma lowerShriekExchangeOfInv_app_comp_map_comp_app_eq_of_unit {ΨN : DN ⥤ DN'}
    {Ψ₁ : D₁ ⥤ D₁'} {Dh₁ : DN ⥤ D₁} {Dh₁' : DN' ⥤ D₁'} {Lπ : D₁ ⥤ DN} {Rπ : DN ⥤ D₁}
    {Lπ' : D₁' ⥤ DN'} {Rπ' : DN' ⥤ D₁'} (adj₁ : Dh₁ ⊣ Lπ) (adj₁' : Dh₁' ⊣ Lπ')
    (adjπ : Lπ ⊣ Rπ) (adjπ' : Lπ' ⊣ Rπ') (α : Ψ₁ ⋙ Lπ' ⟶ Lπ ⋙ ΨN) [IsIso α]
    (χπ : Rπ ⋙ Ψ₁ ⟶ ΨN ⋙ Rπ')
    (hχπ : ∀ A, Lπ'.map (χπ.app A) ≫ adjπ'.counit.app (ΨN.obj A) =
      α.app (Rπ.obj A) ≫ ΨN.map (adjπ.counit.app A))
    (K : DN) (e : Dh₁.obj K ⟶ Rπ.obj K) (e' : Dh₁'.obj (ΨN.obj K) ⟶ Rπ'.obj (ΨN.obj K))
    (hE : adj₁.unit.app K ≫ Lπ.map e ≫ adjπ.counit.app K = 𝟙 K)
    (hE' : adj₁'.unit.app (ΨN.obj K) ≫ Lπ'.map e' ≫ adjπ'.counit.app (ΨN.obj K) = 𝟙 _)
    [IsIso (adj₁'.unit.app (ΨN.obj K))] :
    (lowerShriekExchangeOfInv adj₁ adj₁' α).app K ≫ Ψ₁.map e ≫ χπ.app K = e' := by
  apply (adjπ'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [hχπ, ← cancel_epi (adj₁'.unit.app (ΨN.obj K)), hE']
  have h1 := α.naturality e
  simp only [Functor.comp_map] at h1
  rw [reassoc_of% h1, ← ΨN.map_comp, reassoc_of% (unit_comp_lowerShriekExchangeOfInv_app adj₁
    adj₁' α K), NatIso.isIso_inv_app α, IsIso.inv_hom_id_assoc, ← ΨN.map_comp, hE,
    ΨN.map_id]
  rfl

end Abstract

section Shape

variable {DC DC' DP DP' Ds Ds' : Type*} [Category DC] [Category DC'] [Category DP]
  [Category DP'] [Category Ds] [Category Ds']

/-- **The compact-support exchange of a compactification against a proper exchange**, on the
shape `compactSupportExchangeAux` with restricted functors given as lifts: let
`ν = χ_p⁻¹ ∘ Rp'(ν_h)` be built from `i₁ : LSf' ≅ h'_! ⋙ Rp'` and `i₂ : LSf ≅ h_! ⋙ Rp`, and let
`χ : RC ⋙ Ψs ⟶ ΨC ⋙ RC'` be an exchange satisfying the composition law `hχ` through
`conj : RC ≅ Rπ ⋙ Rp`, `conj'` and `χπ`. If `e : h_! M ⟶ Rπ M`, `e'` satisfy the key identity
`hE`, then `ν_M ≫ z = x` for `z = Ψs(y) ≫ χ_M` (`hz`) and the morphisms `x`, `y` obtained from
`i₁`, `i₂` through `e'`, `e` (`hx`, `hy`). The composite `z` is a separate argument so that it
can be matched syntactically against a goal. -/
lemma compactSupportExchangeAux_lift_app_hom_comp_eq {PC : ObjectProperty DC}
    {PC' : ObjectProperty DC'} {Ps : ObjectProperty Ds} {Ps' : ObjectProperty Ds'}
    {PP : ObjectProperty DP} {PP' : ObjectProperty DP'}
    {LSf' : PC'.FullSubcategory ⥤ Ps'.FullSubcategory}
    {LSf : PC.FullSubcategory ⥤ Ps.FullSubcategory} {ΨC : DC ⥤ DC'} {Ψs : Ds ⥤ Ds'}
    (hSp : ∀ X, PC' ((PC.ι ⋙ ΨC).obj X)) (hT : ∀ X, Ps' ((Ps.ι ⋙ Ψs).obj X))
    {ΨP : DP ⥤ DP'} {Dh : DC ⥤ DP} {Dh' : DC' ⥤ DP'} {Rp : DP ⥤ Ds}
    {Rp' : DP' ⥤ Ds'} (hO : ∀ X, PP ((PC.ι ⋙ Dh).obj X))
    (hO' : ∀ X, PP' ((PC'.ι ⋙ Dh').obj X)) (hR : ∀ X, Ps ((PP.ι ⋙ Rp).obj X))
    (hR' : ∀ X, Ps' ((PP'.ι ⋙ Rp').obj X))
    (i₁ : LSf' ≅ PP'.lift (PC'.ι ⋙ Dh') hO' ⋙ Ps'.lift (PP'.ι ⋙ Rp') hR')
    (i₂ : LSf ≅ PP.lift (PC.ι ⋙ Dh) hO ⋙ Ps.lift (PP.ι ⋙ Rp) hR)
    (νh : ΨC ⋙ Dh' ⟶ Dh ⋙ ΨP) (χp : Rp ⋙ Ψs ⟶ ΨP ⋙ Rp') (hφp : IsIsoOn PP.ι χp)
    {Rπ : DC ⥤ DP} {Rπ' : DC' ⥤ DP'} {RC : DC ⥤ Ds} {RC' : DC' ⥤ Ds'}
    (conj : RC ≅ Rπ ⋙ Rp) (conj' : RC' ≅ Rπ' ⋙ Rp') (χπ : Rπ ⋙ ΨP ⟶ ΨC ⋙ Rπ')
    (χ : RC ⋙ Ψs ⟶ ΨC ⋙ RC') (M : PC.FullSubcategory)
    (hχ : ∀ A, χ.app A = Ψs.map (conj.hom.app A) ≫ χp.app (Rπ.obj A) ≫
      Rp'.map (χπ.app A) ≫ conj'.inv.app (ΨC.obj A))
    (e : Dh.obj M.obj ⟶ Rπ.obj M.obj) (e' : Dh'.obj (ΨC.obj M.obj) ⟶ Rπ'.obj (ΨC.obj M.obj))
    (hE : νh.app M.obj ≫ ΨP.map e ≫ χπ.app M.obj = e')
    (x : (LSf'.obj ((PC'.lift (PC.ι ⋙ ΨC) hSp).obj M)).obj ⟶ RC'.obj (ΨC.obj M.obj))
    (hx : (i₁.hom.app ((PC'.lift (PC.ι ⋙ ΨC) hSp).obj M)).hom ≫ Rp'.map e' ≫
      conj'.inv.app (ΨC.obj M.obj) = x)
    (y : (LSf.obj M).obj ⟶ RC.obj M.obj)
    (hy : (i₂.hom.app M).hom ≫ Rp.map e ≫ conj.inv.app M.obj = y)
    (z : _) (hz : z = Ψs.map y ≫ χ.app M.obj) :
    ((compactSupportExchangeAux Ps'.fullyFaithfulι i₁ i₂ (PC'.liftCompιIso _ hSp)
        (PP'.liftCompιIso _ hO') (Ps'.liftCompιIso _ hR') (PP.liftCompιIso _ hO)
        (Ps.liftCompιIso _ hR) (Ps'.liftCompιIso _ hT) νh
        (invOnSubcategory PP.ι χp hφp)).app M).hom ≫ z = x := by
  subst hz
  have h := compactSupportExchangeAux_app Ps'.fullyFaithfulι i₁ i₂ (PC'.liftCompιIso _ hSp)
    (PP'.liftCompιIso _ hO') (Ps'.liftCompιIso _ hR') (PP.liftCompιIso _ hO)
    (Ps.liftCompιIso _ hR) (Ps'.liftCompιIso _ hT) νh (invOnSubcategory PP.ι χp hφp) M
  simp only [ObjectProperty.ι_map] at h
  have n := χp.naturality e
  simp only [Functor.comp_map] at n
  rw [hχ, ← hx, ← hy, h]
  simp only [ObjectProperty.liftCompιIso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.assoc, Functor.map_comp]
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, ObjectProperty.lift_obj_obj,
    CategoryTheory.Functor.map_id, Category.id_comp, ObjectProperty.lift_map,
    ObjectProperty.homMk_hom, Functor.comp_map, ObjectProperty.ι_map]
  rw [← Ψs.map_comp_assoc (conj.inv.app _), Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, reassoc_of% n, ← Ψs.map_comp_assoc, ← ObjectProperty.FullSubcategory.comp_hom,
    Iso.inv_hom_id_app, ObjectProperty.FullSubcategory.id_hom]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, invOnSubcategory_app_comp_assoc]
  simp only [← hE, Functor.map_comp, Category.assoc]

end Shape

section OpenProper

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {U X S : Over (Spec (.of k))} [LocallyOfFiniteType U.hom]
  [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]

/-- The unit of the derived adjunction `j_! ⊣ Lj^*` along an open immersion is an isomorphism. -/
instance isIso_openImmersionAdjunction_unit_app {V W : Scheme.{u}} (j : V ⟶ W)
    [IsOpenImmersion j] (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V))) :
    IsIso ((openImmersionAdjunction ℓ j).unit.app M) := by
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) j).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

/-- **The canonical map of an open and proper immersion inverts the unit**, on the ambient
derived categories: for an open immersion `j` which is proper, the adjoint
`Lj^*(e) ≫ ε : Lj^* j_! M ⟶ M` of `e : j_! M ≅ Rj_! M ≅ Rj_* M` is a left inverse of the unit
of `j_! ⊣ Lj^*`. -/
lemma openImmersionAdjunction_unit_app_comp_map_comp_counit_app (j : U ⟶ X)
    [IsOpenImmersion j.left] [IsProper j.left] (M : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (openImmersionAdjunction ℓ j.left).unit.app M.obj ≫
        L((j.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
          ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app M ≫
            (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).hom.app M).hom ≫
        (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) j.left).counit.app
          M.obj =
      𝟙 M.obj := by
  have h := congrArg (fun f ↦ f.hom)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_clopen_of j ℓ
      (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_inv_app_comp_counit j ℓ) M)
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    openImmersionLowerShriekUpperStarAdjunction_unit_app_hom, boundedConstructibleUpperStar_map_hom,
    boundedConstructibleUpperStarLowerStarAdjunction_counit_app_hom,
    ObjectProperty.FullSubcategory.id_hom] at h
  exact h

/-- **The factorization of `Ra_!` through an open and proper immersion**: for an open immersion
`j : U ⟶ X` which is proper and a proper `a₁ : X ⟶ S` with `j ≫ a₁ = a`, the factorization
`Ra_! ≅ j_! ⋙ Ra₁_*` (`compactificationLowerShriekIso`), followed by `Ra₁_*` of
`j_! ≅ Rj_! ≅ Rj_*` and `Rj_* ⋙ Ra₁_* ≅ Ra_*`, is `Ra_! ≅ Ra_*`. -/
lemma compactificationLowerShriekIso_hom_app_comp_map_comp_lowerStarCompOfEq_hom_app
    (j : U ⟶ X) (a₁ : X ⟶ S) (a : U ⟶ S) [IsOpenImmersion j.left] [IsProper j.left]
    [IsProper a₁.left] [IsProper a.left] (w : j ≫ a₁ = a)
    (K : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (compactificationLowerShriekIso ℓ j a₁ w).hom.app K ≫
        (boundedConstructibleLowerStar ℓ a₁).map
          ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app K ≫
            (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).hom.app K) ≫
        (boundedConstructibleLowerStarCompOfEq ℓ j a₁ w).hom.app K =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ a).hom.app K := by
  subst w
  simp only [compactificationLowerShriekIso, lowerShriekCompOfEq,
    boundedConstructibleLowerStarCompOfEq, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc, Functor.map_comp, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  have n := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ a₁).hom.naturality
    ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app K)
  rw [← reassoc_of% n, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp,
    isoLowerStar_hom_app_comp_map_comp_lowerStarComp_hom ℓ j a₁ K, Iso.hom_inv_id_app_assoc]

/-- `compactificationLowerShriekIso_hom_app_comp_map_comp_lowerStarCompOfEq_hom_app` on the
ambient derived categories, with the restricted functors written as lifts of the ambient ones
(as in `compactSupportExchangeOfCompactification_eq_lift`) and `Rj_* ⋙ Ra₁_* ≅ Ra_*` as the
conjugate of `La^* ≅ La₁^* ⋙ Lj^*`. -/
lemma compactificationLowerShriekIso_hom_app_hom_comp_map_comp_conjugateIsoEquiv_inv_app
    (j : U ⟶ X) (a₁ : X ⟶ S) (a : U ⟶ S) [IsOpenImmersion j.left] [IsProper j.left]
    [IsProper a₁.left] [IsProper a.left] (w : j ≫ a₁ = a)
    (K : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((Iso.hom (X := boundedConstructibleLowerShriek ℓ a)
        (Y := (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
            D((j.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧))
            (fun K ↦ ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).obj K).property) ⋙
          (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
            R((a₁.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
            (fun K ↦ ((boundedConstructibleLowerStar ℓ a₁).obj K).property))
        (compactificationLowerShriekIso ℓ j a₁ w)).app K).hom ≫
      R((a₁.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app K ≫
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).hom.app K).hom ≫
      (conjugateIsoEquiv
        (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) a.left)
        ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) a₁.left).comp
          (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) j.left))
        (leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ)
          (congrArg CommaMorphism.left w)).symm).inv.app K.obj =
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ a).hom.app K).hom := by
  have h := congrArg (fun f ↦ f.hom)
    (compactificationLowerShriekIso_hom_app_comp_map_comp_lowerStarCompOfEq_hom_app ℓ j a₁ a w K)
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleLowerStar_map_hom,
    boundedConstructibleLowerStarCompOfEq_hom_app_hom] at h
  exact h

/-- `compactificationLowerShriekIso_hom_app_hom_comp_map_comp_conjugateIsoEquiv_inv_app` on the
restriction `K = Ψ M` of a functor `Ψ` preserving bounded constructible complexes. -/
lemma compactificationLowerShriekIso_hom_app_hom_comp_map_comp_conjugateIsoEquiv_inv_app_lift
    (j : U ⟶ X) (a₁ : X ⟶ S) (a : U ⟶ S) [IsOpenImmersion j.left] [IsProper j.left]
    [IsProper a₁.left] [IsProper a.left] (w : j ≫ a₁ = a) {Z : Scheme.{u}}
    (Ψ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left)))
    (hΨ : ∀ K : Dᵇc(Z)⟦Profinite.padicAlgClRingObj ℓ⟧,
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left)
        (Ψ.obj K.obj))
    (M : Dᵇc(Z)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((Iso.hom (X := boundedConstructibleLowerShriek ℓ a)
        (Y := (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
            D((j.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧))
            (fun K ↦ ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).obj K).property) ⋙
          (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
            R((a₁.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
            (fun K ↦ ((boundedConstructibleLowerStar ℓ a₁).obj K).property))
        (compactificationLowerShriekIso ℓ j a₁ w)).app
          (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙ Ψ) hΨ).obj M)).hom ≫
      R((a₁.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app
            (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙ Ψ) hΨ).obj M) ≫
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).hom.app
            (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙ Ψ) hΨ).obj M)).hom ≫
      (conjugateIsoEquiv
        (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) a.left)
        ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) a₁.left).comp
          (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) j.left))
        (leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ)
          (congrArg CommaMorphism.left w)).symm).inv.app (Ψ.obj M.obj) =
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ a).hom.app
      (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙ Ψ) hΨ).obj M)).hom :=
  compactificationLowerShriekIso_hom_app_hom_comp_map_comp_conjugateIsoEquiv_inv_app ℓ j a₁ a w _

end OpenProper

section General

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {Y X : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {Y' X' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
  [IsSeparated Y'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [IsProper (toPoint Y).left] [IsProper (toPoint X).left] [IsProper (toPoint Y').left]
  [IsProper (toPoint X').left]
  {ι : Y ⟶ X} {ι' : Y' ⟶ X'} [IsOpenImmersion ι.left] [IsOpenImmersion ι'.left]
  [IsProper ι.left] [IsProper ι'.left]
  {N : NearbyCyclesModel Y.left Y'.left} {P : NearbyCyclesModel X.left X'.left}
  (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  {T : NearbyCyclesModel (point k).left (point k').left}
  (hS : T.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))

omit [IsProper (toPoint Y).left] [IsProper (toPoint Y').left] in
/-- On the ambient derived categories, `Ψ_S(f)` followed by the restricted proper exchange `χ_a`
is `Ψ_S(f)` followed by the ambient `χ_a`. -/
lemma map_hom_comp_boundedConstructiblePushforwardExchange_app_hom
    (a : N.Hom T (toPoint Y).left (toPoint Y').left)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (f : (boundedConstructibleLowerShriek ℓ (toPoint Y)).obj K ⟶
      (boundedConstructibleLowerStar ℓ (toPoint Y)).obj K) :
    ((NearbyCyclesModel.boundedConstructibleNearbyCycles hS).map f).hom ≫
        ((a.boundedConstructiblePushforwardExchange ℓ hN hS).app K).hom =
      (T.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map
          (Y := R(((toPoint Y).left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K.obj) f.hom ≫
        (a.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K.obj := by
  rw [NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_app_hom]
  rfl

/-- **The compact-support exchange of a compactification of a proper model inverts the proper
exchange**: for a compactification `φ : N ⟶ P` over open and proper `ι`, `ι'`, with structure
morphisms `a₁` of `P` and `a = φ ≫ a₁` of `N` to the trait, the exchange
`ν = χ_{a₁}⁻¹ ∘ Ra'_{1*}(ν_ι)` followed by `Ra_! ≅ Ra_*` and `χ_a` is `Ra'_! ≅ Ra'_*`. -/
theorem compactSupportExchangeOfCompactification_app_comp_map_comp_pushforwardExchange_app
    (φ : N.Hom P ι.left ι'.left) [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    (a₁ : P.Hom T (toPoint X).left (toPoint X').left)
    (ha₁ : IsIsoOn (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      X.left)).ι (a₁.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)))
    (a : N.Hom T (toPoint Y).left (toPoint Y').left)
    (htot : φ.total ≫ a₁.total = a.total) (hgen : φ.generic ≫ a₁.generic = a.generic)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (compactSupportExchangeOfCompactification ℓ hN hS (comp_toPoint ι) (comp_toPoint ι') φ a₁
        ha₁).app K ≫
        (NearbyCyclesModel.boundedConstructibleNearbyCycles hS).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Y)).hom.app K) ≫
        (a.boundedConstructiblePushforwardExchange ℓ hN hS).app K =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Y')).hom.app
        ((NearbyCyclesModel.boundedConstructibleNearbyCycles hN).obj K) := by
  ext1
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    compactSupportExchangeOfCompactification_eq_lift,
    map_hom_comp_boundedConstructiblePushforwardExchange_app_hom]
  apply compactSupportExchangeAux_lift_app_hom_comp_eq
    (conj := conjugateIsoEquiv
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) (toPoint Y).left)
      ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
        (toPoint X).left).comp
        (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ι.left))
      (leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ)
        (congrArg CommaMorphism.left (comp_toPoint ι))).symm)
    (conj' := conjugateIsoEquiv
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) (toPoint Y').left)
      ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
        (toPoint X').left).comp
        (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ι'.left))
      (leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ)
        (congrArg CommaMorphism.left (comp_toPoint ι'))).symm)
    (χπ := φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ))
    (χ := a.pushforwardExchange (Profinite.padicAlgClRingObj ℓ))
    (y := ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Y)).hom.app K).hom)
    (e := ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ ι).inv.app K ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ ι).hom.app K).hom)
    (e' := ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ ι').inv.app
        (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙
          N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)) fun K ↦ hN K.obj K.property).obj K) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ ι').hom.app
        (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙
          N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)) fun K ↦ hN K.obj K.property).obj K)).hom)
  case hχ =>
    intro A
    rw [← reassoc_of% φ.pushforwardExchange_comp_app_of_eq (Profinite.padicAlgClRingObj ℓ) a₁ a
      (congrArg CommaMorphism.left (comp_toPoint ι))
      (congrArg CommaMorphism.left (comp_toPoint ι')) htot hgen A, Iso.hom_inv_id_app,
      Category.comp_id]
  case hE =>
    apply lowerShriekExchangeOfInv_app_comp_map_comp_app_eq_of_unit
      (adjπ := derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ι.left)
      (adjπ' := derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ι'.left)
    case hχπ => exact φ.map_pushforwardExchange_app_comp_counit_app (Profinite.padicAlgClRingObj ℓ)
    case hE => exact openImmersionAdjunction_unit_app_comp_map_comp_counit_app ℓ ι K
    case hE' =>
      exact openImmersionAdjunction_unit_app_comp_map_comp_counit_app ℓ ι'
        (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙
          N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)) fun K ↦ hN K.obj K.property).obj K)
  case hx =>
    cast_proofs
      compactificationLowerShriekIso_hom_app_hom_comp_map_comp_conjugateIsoEquiv_inv_app_lift ℓ ι'
        (toPoint X') (toPoint Y') (comp_toPoint ι') (N.nearbyCycles (Profinite.padicAlgClRingObj ℓ))
        (fun K ↦ hN K.obj K.property) K
  case hy =>
    cast_proofs compactificationLowerShriekIso_hom_app_hom_comp_map_comp_conjugateIsoEquiv_inv_app
      ℓ ι (toPoint X) (toPoint Y) (comp_toPoint ι) K
  case hz =>
    cast_proofs Eq.refl ((T.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map
      (Y := R(((toPoint Y).left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K.obj)
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Y)).hom.app K).hom ≫
      (a.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K.obj)

end General

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [Algebra k k']

namespace IsTraitModelOfBase

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom]
  [QuasiCompact Y'.hom] [IsSeparated Y'.hom] {N : NearbyCyclesModel Y.left Y'.left}
  {q : N.total ⟶ trait k'} {g : N.generic ⟶ Spec (.of (traitGenericField k'))}

/-- **The compact-support exchange of a proper model is the inverse of the proper exchange**: for
a trait model `N` of a proper `Y` with proper special fibre and a compactification `C`, the
exchange `ν_C` followed by `Ra_! ≅ Ra_*` and the proper exchange `χ_a` is `Ra'_! ≅ Ra'_*`. -/
theorem Compactification.compactSupportExchange_app_comp_map_comp_pushforwardExchange_app
    [IsProper (toPoint Y).left] [IsProper (toPoint Y').left] {h : N.IsTraitModelOfBase k q g}
    (C : h.Compactification) (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (C.compactSupportExchange ℓ).app K ≫
        (traitSpecialization k k' (ℓ := ℓ)).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Y)).hom.app K) ≫
        (h.pushforwardExchange ℓ).app K =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Y')).hom.app
        ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ)).obj K) := by
  have : IsProper C.ι.left := by
    have : IsProper (C.ι.left ≫ C.X.hom) := by
      rw [Over.w, ← toPoint_left]
      infer_instance
    exact IsProper.of_comp C.ι.left C.X.hom
  have : IsProper C.ι'.left := by
    have : IsProper (C.ι'.left ≫ C.X'.hom) := by
      rw [Over.w, ← toPoint_left]
      infer_instance
    exact IsProper.of_comp C.ι'.left C.X'.hom
  -- rewriting first makes the instances of the goal those of the general statement
  have e₂ : h.pushforwardExchange ℓ = Hom.boundedConstructiblePushforwardExchange
      (f := toPoint Y) (f' := toPoint Y') ℓ h.toTrait (h.preservesBoundedConstructible ℓ)
      (preservesBoundedConstructible_traitModel ℓ) := rfl
  rw [Compactification.compactSupportExchange, e₂]
  delta traitSpecialization
  cast_proofs compactSupportExchangeOfCompactification_app_comp_map_comp_pushforwardExchange_app ℓ
    (h.preservesBoundedConstructible ℓ) (preservesBoundedConstructible_traitModel ℓ) C.hom
    C.isTraitModelOfBase.toTrait (C.isIsoOn_pushforwardExchange ℓ) h.toTrait C.q_eq.symm
    C.g_eq.symm K

end IsTraitModelOfBase

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
