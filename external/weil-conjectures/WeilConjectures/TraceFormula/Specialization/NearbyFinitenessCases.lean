/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLisseDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.TraceFormula.Specialization.NearbyProperExchange
public import WeilConjectures.TraceFormula.Specialization.TraitModelEmbedding
public import WeilConjectures.TraceFormula.Specialization.TraitNearbyFiniteness

/-!

# Special cases of Deligne's finiteness theorem for nearby cycles on affine spaces

Over the strictly henselian trait `S = Spec k'⟦t⟧`, this file proves the reductions and special
cases used for Deligne's finiteness theorem for nearby cycles
(`WeilConjectures.TraceFormula.Specialization.NearbyFiniteness`) on the affine spaces `𝔸ⁿ_S`:

* the reduction along a closed embedding of models
  (`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj_of_closedEmbedding`);
* extensions by zero of lisse sheaves are bounded constructible
  (`NearbyCyclesModel.boundedConstructible_lisseExtension`);
* the case `n = 0` (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpaceModel_zero`);
* complexes supported on a closed subscheme missing the special fibre have vanishing nearby
  cycles (`NearbyCyclesModel.isZero_nearbyCycles_affineSpace_of_disjoint`), and those supported on
  a closed subscheme embedded in the trait have bounded constructible nearby cycles
  (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_of_isClosedImmersion_comp`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] {X : Scheme.{u}}
  {X' : Over (Spec (.of k'))}

/-- The special fibre of a model of finite type over the trait is a noetherian scheme: it is of
finite type over the field `k'`. -/
lemma isNoetherian_of_isTraitModel {M : NearbyCyclesModel X X'.left} (hM : M.IsTraitModel) :
    IsNoetherian X'.left := by
  obtain ⟨q, g, _, _, _, -, hi⟩ := hM.exists_isPullback
  have : LocallyOfFiniteType X'.hom :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hi ‹_›
  have : QuasiCompact X'.hom := MorphismProperty.of_isPullback (P := @QuasiCompact) hi ‹_›
  have : IsLocallyNoetherian X'.left := LocallyOfFiniteType.isLocallyNoetherian X'.hom
  have : CompactSpace X'.left := QuasiCompact.compactSpace_of_compactSpace X'.hom
  exact ⟨⟩

/-- The standard model of the affine space `𝔸ⁿ_S` over the trait `S = Spec k'⟦t⟧`. -/
noncomputable abbrev affineSpaceModel (k' : Type u) [Field k'] (n : ℕ) :=
  traitStdModel (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')

/-- The standard model of `𝔸ⁿ_S` is a model of finite type over the trait. -/
lemma isTraitModel_affineSpaceModel (n : ℕ) : (affineSpaceModel k' n).IsTraitModel :=
  isTraitModel_traitStdModel _

/-- The derived pullbacks along equal morphisms agree on objects. -/
lemma nonempty_leftDerivedUpperStar_obj_iso_of_eq (Λ : Sheaf (coherentTopology Profinite.{u})
    Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] {Y Z : Scheme.{u}} {a b : Y ⟶ Z} (h : a = b)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    Nonempty ((L((a)^*⟦Λ⟧)).obj K ≅ (L((b)^*⟦Λ⟧)).obj K) := by
  subst h
  exact ⟨Iso.refl _⟩

variable (k') in
/-- The generic fibre `S ∖ {s} = D(t)` of the trait `S = Spec k'⟦t⟧`, as an open subscheme. -/
noncomputable def traitGenericOpen : (trait k').Opens :=
  (trait k').basicOpen ((Scheme.ΓSpecIso (.of (PowerSeries k'))).inv PowerSeries.X)

/-- The geometric generic point of the trait lies in its generic fibre `D(t)`: `t` is a nonzero
element of the field `Ω`. -/
lemma traitGenericPoint_preimage_traitGenericOpen :
    traitGenericPoint k' ⁻¹ᵁ traitGenericOpen k' = ⊤ := by
  rw [traitGenericOpen, Scheme.preimage_basicOpen_top, traitGenericPoint,
    ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
    Scheme.basicOpen_of_isUnit]
  refine IsUnit.map _ (Ne.isUnit ?_)
  change algebraMap (PowerSeries k') (traitGenericField k') PowerSeries.X ≠ 0
  rw [IsScalarTower.algebraMap_apply (PowerSeries k') (FractionRing (PowerSeries k'))]
  exact (map_ne_zero _).2 (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero PowerSeries.X_ne_zero))

/-- The closed point of the trait does not lie in its generic fibre `D(t)`. -/
lemma traitClosedPoint_preimage_traitGenericOpen :
    traitClosedPoint k' ⁻¹ᵁ traitGenericOpen k' = ⊥ := by
  rw [traitGenericOpen, Scheme.preimage_basicOpen_top, traitClosedPoint,
    ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  change Scheme.basicOpen _ ((Scheme.ΓSpecIso (.of k')).inv
    (PowerSeries.constantCoeff PowerSeries.X)) = ⊥
  rw [PowerSeries.constantCoeff_X, map_zero, Scheme.basicOpen_zero]

variable (k') in
/-- The generic fibre `𝔸ⁿ_η` of the affine space `𝔸ⁿ_S`, as an open subscheme: the preimage of
the generic fibre `D(t)` of the trait. -/
noncomputable def affineSpaceGenericOpen (n : ℕ) : (affineSpaceModel k' n).total.Opens :=
  (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k') ⁻¹ᵁ traitGenericOpen k'

/-- The geometric generic fibre `𝔸ⁿ_η̄ ⟶ 𝔸ⁿ_S` lands in the generic fibre `𝔸ⁿ_η`. -/
lemma range_j_affineSpaceModel_subset (n : ℕ) :
    Set.range (affineSpaceModel k' n).j.base ⊆
      Set.range (affineSpaceGenericOpen k' n).ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨y, rfl⟩
  change y ∈ (affineSpaceModel k' n).j ⁻¹ᵁ affineSpaceGenericOpen k' n
  rw [affineSpaceGenericOpen, ← Scheme.Hom.comp_preimage]
  simp only [affineSpaceModel, traitStdModel_j, pullback.condition, Scheme.Hom.comp_preimage,
    traitGenericPoint_preimage_traitGenericOpen, Scheme.Hom.preimage_top]
  trivial

/-- **Nearby cycles of a complex supported on the special fibre vanish**: if `Rc_* K` is a
complex on `𝔸ⁿ_S` pushed forward along a closed immersion `c : D ⟶ 𝔸ⁿ_S`, and the restriction of
`K` to the generic fibre `c⁻¹ 𝔸ⁿ_η` vanishes, then `Lj^* Rc_* K = 0`, so the geometric nearby
cycles `Li^* Rj_* Lj^* Rc_* K` vanish. -/
lemma isZero_nearbyCycles_affineSpace_of_isZero (n : ℕ) {D : Scheme.{u}}
    (c : D ⟶ (affineSpaceModel k' n).total) [IsClosedImmersion c]
    [QuasiCompact (c ⁻¹ᵁ affineSpaceGenericOpen k' n).ι]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) D))}
    (hK : IsZero ((L(((c ⁻¹ᵁ affineSpaceGenericOpen k' n).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
      K)) :
    IsZero (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
      ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)) := by
  have h := isZero_leftDerivedUpperStar_ι_obj_rightDerivedLowerStar_obj
    (Profinite.padicAlgClRingObj ℓ) (affineSpaceGenericOpen k' n) c hK
  have hfac := IsOpenImmersion.lift_fac (affineSpaceGenericOpen k' n).ι
    (affineSpaceModel k' n).j (range_j_affineSpaceModel_subset n)
  have i₁ := (nonempty_leftDerivedUpperStar_obj_iso_of_eq (Profinite.padicAlgClRingObj ℓ)
    hfac.symm ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)).some
  have i₂ := (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ)
    (IsOpenImmersion.lift (affineSpaceGenericOpen k' n).ι (affineSpaceModel k' n).j
      (range_j_affineSpaceModel_subset n)) (affineSpaceGenericOpen k' n).ι).app
    ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)
  exact (L(((affineSpaceModel k' n).geometric.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map_isZero
    ((R(((affineSpaceModel k' n).geometric.j)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).map_isZero
      (((L((IsOpenImmersion.lift (affineSpaceGenericOpen k' n).ι (affineSpaceModel k' n).j
        (range_j_affineSpaceModel_subset n))^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map_isZero
          h).of_iso (i₁ ≪≫ i₂)))

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

omit [IsSepClosed k'] [Fact (ringChar k').Prime] in
/-- **Reduction along a closed embedding**: let `φ : M.geometric ⟶ N.geometric` be a morphism of
the geometric models of two models of finite type over the trait, whose morphism of total spaces
`t` is a closed immersion and whose squares of geometric generic fibres and of special fibres are
cartesian. If the geometric nearby cycles of `N` preserve bounded constructible complexes, then
so do those of `M`: `Ψ_M B ≅ Lt_s^* Rt_{s*} Ψ_M B ≅ Lt_s^* Ψ_N (Rt_* B)` by the full faithfulness
of `Rt_{s*}` and the proper exchange
(`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_geometric`), and `Rt_* B` is
bounded constructible. -/
theorem boundedConstructible_geometricNearbyCycles_obj_of_closedEmbedding {Y : Scheme.{u}}
    {Y' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
    {N : NearbyCyclesModel Y Y'.left} (hM : M.IsTraitModel) (hN : N.IsTraitModel)
    {t : M.total ⟶ N.total} {f' : X'.left ⟶ Y'.left} (φ : M.geometric.Hom N.geometric t f')
    (ht : φ.total = t) [IsClosedImmersion t] (hj : IsPullback φ.generic M.j N.j t)
    (hi : IsPullback M.i f' t N.i)
    (hN' : ∀ {B' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) N.total))},
      boundedConstructible _ B' → boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y'.left)
        ((N.geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B'))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X'.left)
      ((M.geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B) := by
  have := hN.isNoetherian_total
  have : IsClosedImmersion f' := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hi ‹_›
  have : IsProper t := inferInstance
  have : IsIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app B) :=
    Hom.isIso_pushforwardExchange_app_of_isProper_geometric φ hM hN ht hj hi B hB
  have h₁ : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y'.left)
      ((N.geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        ((R((t)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj B)) :=
    hN' (boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion _ t hB)
  have h₂ : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y'.left)
      ((R((f')_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
        ((M.geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B)) :=
    (boundedConstructible _).prop_of_iso
      (asIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app B)) h₁
  exact (boundedConstructible _).prop_of_iso
    (asIso ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f').counit.app _))
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f' _ h₂)

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- The extension by zero `j_{W!} Rc'_* L` of a lisse sheaf `L` on `E` along a closed immersion
`c' : E ⟶ W` into an open `W` of a closed subscheme `c : D ⟶ 𝔸ⁿ_S` is a bounded constructible
complex on `D`. -/
lemma boundedConstructible_lisseExtension_closed (n : ℕ) (D : Scheme.{u})
    (c : D ⟶ (affineSpaceModel k' n).total) [IsClosedImmersion c] (W : D.Opens) (E : Scheme.{u})
    (c' : E ⟶ W) [IsClosedImmersion c']
    (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E))
    (hL : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E) L) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) D)
      (D((W.ι)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        ((R((c')_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          ((DerivedCategory.singleFunctor _ 0).obj L))) := by
  have : IsNoetherian (affineSpaceModel k' n).total :=
    (isTraitModel_affineSpaceModel (k' := k') n).isNoetherian_total
  have : TopologicalSpace.NoetherianSpace D := c.isClosedEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace W := W.ι.isOpenEmbedding.isInducing.noetherianSpace
  have hL' : IsConstructibleModuleObject _ L :=
    ⟨Scheme.Stratification.trivial E, fun _ ↦ (isLocallyFinitelyPresented_mapMod_iff _ _ _).2
      (IsLocallyFinitelyPresented.upperStar _ _ hL)⟩
  exact boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj _ W.ι _
    (boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion _ c'
      (boundedConstructible_singleFunctor_zero_obj _ L hL'))

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- The extension by zero `v_! L = Rc_* j_{W!} Rc'_* L` of a lisse sheaf `L` along a locally closed
immersion `v : E ⟶ 𝔸ⁿ_S`, factored through a closed immersion `c' : E ⟶ W` into an open `W` of a
closed subscheme `c : D ⟶ 𝔸ⁿ_S`, is a bounded constructible complex on `𝔸ⁿ_S`. -/
lemma boundedConstructible_lisseExtension (n : ℕ) (D : Scheme.{u})
    (c : D ⟶ (affineSpaceModel k' n).total) [IsClosedImmersion c] (W : D.Opens) (E : Scheme.{u})
    (c' : E ⟶ W) [IsClosedImmersion c']
    (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E))
    (hL : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E) L) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (affineSpaceModel k' n).total)
      ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
        (D((W.ι)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          ((R((c')_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
            ((DerivedCategory.singleFunctor _ 0).obj L)))) := by
  have : IsNoetherian (affineSpaceModel k' n).total :=
    (isTraitModel_affineSpaceModel (k' := k') n).isNoetherian_total
  exact boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion _ c
    (boundedConstructible_lisseExtension_closed n D c W E c' L hL)

omit [Fact (ringChar k').Prime] in
/-- **Deligne's finiteness theorem for nearby cycles on `𝔸⁰_S`**: the geometric nearby cycles of
the standard model of `𝔸⁰_S` preserve bounded constructible complexes. The structure map
`q : 𝔸⁰_S ⟶ S` is an isomorphism, hence a closed embedding with cartesian squares of fibres into
the trait, whose nearby cycles preserve bounded constructible complexes
(`NearbyCyclesModel.preservesBoundedConstructible_traitSelfModel`). -/
theorem boundedConstructible_nearbyCycles_affineSpaceModel_zero
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' 0).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (affineSpaceModel k' 0).total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin 0); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' 0).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        B) := by
  let q := 𝔸(ULift.{u} (Fin 0); trait k') ↘ trait k'
  have : IsClosedImmersion q :=
    inferInstanceAs (IsClosedImmersion (𝔸(ULift.{u} (Fin 0); trait k') ↘ trait k'))
  let φ : (affineSpaceModel k' 0).geometric.Hom (traitSelfModel k').geometric q
      (pullback.snd q (traitClosedPoint k')) :=
    { total := q
      generic := pullback.snd q (traitGenericPoint k')
      comm_j := pullback.condition.symm
      comm_i := pullback.condition.symm
      comm_ε := pullback.condition.symm }
  exact boundedConstructible_geometricNearbyCycles_obj_of_closedEmbedding
    (Y' := Over.mk (𝟙 (Spec (.of k')))) (N := traitSelfModel k') (isTraitModel_affineSpaceModel 0)
    (isTraitModel_traitSelfModel k') φ rfl
    (IsPullback.of_hasPullback q (traitGenericPoint k')).flip
    (IsPullback.of_hasPullback q (traitClosedPoint k'))
    (fun hB' ↦ preservesBoundedConstructible_traitSelfModel k' _ hB') hB

omit [IsSepClosed k'] [Fact (ringChar k').Prime] in
/-- **Nearby cycles of a complex supported away from the special fibre vanish**: if the closed
subscheme `c : D ⟶ 𝔸ⁿ_S` misses the special fibre `𝔸ⁿ_s`, then `Ψ (Rc_* K) = 0` for every bounded
constructible `K` on `D`. By the proper exchange, `Ψ_{𝔸ⁿ} (Rc_* K) ≅ Rc_{s*} Ψ_D K`, and the
special fibre `D_s` of `D` is empty. -/
lemma isZero_nearbyCycles_affineSpace_of_disjoint (n : ℕ) {D : Scheme.{u}}
    (c : D ⟶ (affineSpaceModel k' n).total) [IsClosedImmersion c]
    (hc : Disjoint (Set.range c.base) (Set.range (affineSpaceModel k' n).i.base))
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) D))}
    (hK : boundedConstructible _ K) :
    IsZero (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
      ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)) := by
  let q := 𝔸(ULift.{u} (Fin n); trait k') ↘ trait k'
  let M := traitStdModel (c ≫ q)
  have hj : IsPullback M.j (pullback.snd (c ≫ q) (traitGenericPoint k')) (c ≫ q)
      (traitGenericPoint k') := IsPullback.of_hasPullback _ _
  have hi : IsPullback M.i (traitStdSpecialFibre (c ≫ q)).hom (c ≫ q) (traitClosedPoint k') :=
    IsPullback.of_hasPullback _ _
  let φ := traitStdHom q hj hi c rfl
  have : IsEmpty (traitStdSpecialFibre (c ≫ q)).left := by
    refine ⟨fun x ↦ Set.disjoint_left.1 hc ⟨M.i.base x, rfl⟩
      ⟨(traitStdSpecialHom q hi c rfl).base x, ?_⟩⟩
    exact congrArg (fun g ↦ g.base x) φ.comm_i
  have : IsIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K) :=
    Hom.isIso_pushforwardExchange_app_of_isProper_geometric φ (isTraitModel_traitStdModel _)
      (isTraitModel_affineSpaceModel n) rfl
      (isPullback_traitStdHom_generic q hj hi c rfl) (isPullback_traitStdHom_special q hi c rfl)
      K hK
  refine IsZero.of_iso ?_ (asIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K))
  exact (R((traitStdSpecialHom q hi c rfl)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).map_isZero
    (isZero_derivedCategory_of_isEmpty' _ _)

omit [Fact (ringChar k').Prime] in
/-- **Nearby cycles of a complex supported on a closed subscheme embedded in the trait**: if the
closed subscheme `c : D ⟶ 𝔸ⁿ_S` maps by a closed immersion to the trait `S` (for instance the
closure of an `S`-integral point of the generic fibre), then `Ψ (Rc_* K)` is bounded constructible
for every bounded constructible `K` on `D`. By the closed-embedding reduction along `D ⟶ S`, the
nearby cycles of `D` preserve bounded constructible complexes, the trait's do
(`NearbyCyclesModel.preservesBoundedConstructible_traitSelfModel`); and by the proper exchange,
`Ψ_{𝔸ⁿ} (Rc_* K) ≅ Rc_{s*} Ψ_D K`. -/
theorem boundedConstructible_nearbyCycles_affineSpace_of_isClosedImmersion_comp (n : ℕ)
    {D : Scheme.{u}} (c : D ⟶ (affineSpaceModel k' n).total) [IsClosedImmersion c]
    (hcq : IsClosedImmersion (c ≫ (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')))
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) D))}
    (hK : boundedConstructible _ K) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)) := by
  let q := 𝔸(ULift.{u} (Fin n); trait k') ↘ trait k'
  let M := traitStdModel (c ≫ q)
  have hj : IsPullback M.j (pullback.snd (c ≫ q) (traitGenericPoint k')) (c ≫ q)
      (traitGenericPoint k') := IsPullback.of_hasPullback _ _
  have hi : IsPullback M.i (traitStdSpecialFibre (c ≫ q)).hom (c ≫ q) (traitClosedPoint k') :=
    IsPullback.of_hasPullback _ _
  let ψ : M.geometric.Hom (traitSelfModel k').geometric (c ≫ q)
      (pullback.snd (c ≫ q) (traitClosedPoint k')) :=
    { total := c ≫ q
      generic := pullback.snd (c ≫ q) (traitGenericPoint k')
      comm_j := pullback.condition.symm
      comm_i := pullback.condition.symm
      comm_ε := pullback.condition.symm }
  have hΨ : boundedConstructible _ ((M.geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
      K) :=
    boundedConstructible_geometricNearbyCycles_obj_of_closedEmbedding
      (Y' := Over.mk (𝟙 (Spec (.of k')))) (N := traitSelfModel k')
      (isTraitModel_traitStdModel _) (isTraitModel_traitSelfModel k') ψ rfl hj.flip hi
      (fun hB' ↦ preservesBoundedConstructible_traitSelfModel k' _ hB') hK
  let φ := traitStdHom q hj hi c rfl
  have : IsIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K) :=
    Hom.isIso_pushforwardExchange_app_of_isProper_geometric φ (isTraitModel_traitStdModel _)
      (isTraitModel_affineSpaceModel n) rfl
      (isPullback_traitStdHom_generic q hj hi c rfl) (isPullback_traitStdHom_special q hi c rfl)
      K hK
  have := isNoetherian_of_isTraitModel (isTraitModel_affineSpaceModel (k' := k') n)
  have := isClosedImmersion_traitStdSpecialHom q hi c rfl
  exact (boundedConstructible _).prop_of_iso
    (asIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K)).symm
    (boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion _ _ hΨ)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
