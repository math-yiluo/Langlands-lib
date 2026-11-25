/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero
public import WeilConjectures.WeilSheaf.LowerStar

/-!
# Direct images of Weil sheaves along an open immersion

The ordinary direct image `j_*`, the higher direct images `Rⁱj_*`, the extension by zero `j_!`
and the canonical map `j_! ⟶ j_*` along an open immersion `j`. The direct images are the
pushforwards `WeilSheaf.lowerStar` and `WeilSheaf.higherLowerStar` along `j`. The extension by
zero is the pro-étale extension by zero along the base change `j̄ : Ū ⟶ X̄`, with the Weil
structure transported along `ProEtale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso`.
The map `j_! ⟶ j_*` is the comparison `j̄_! ⟶ j̄_*` of pro-étale sheaves, which is compatible
with these Weil structures
(`ProEtale.openImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso`).

## Main declarations

- `AlgebraicGeometry.WeilSheaf.higherDirectImage`: the higher direct images `Rⁱj_*`.
- `AlgebraicGeometry.WeilSheaf.directImage`, `AlgebraicGeometry.WeilSheaf.extensionByZero` and
  `AlgebraicGeometry.WeilSheaf.extensionByZeroToDirectImage`: the two extensions along an open
  immersion and the canonical map between them.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- Extension by zero `j_!` of pro-étale Weil sheaves along an open immersion `j`: the
pro-étale extension by zero along the base change `j̄ : Ū ⟶ X̄`, with the Weil structure
transported along `ProEtale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def ProEtaleWeilSheaf.extensionByZero (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    ProEtaleWeilSheaf k₀ l U ⥤ ProEtaleWeilSheaf k₀ l X :=
  IsoAlgebra.mapOfNatIso
    (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l j (comp_over j _))

variable (k₀ l) in
/-- The comparison `j_! ⟶ j_*` of pro-étale Weil sheaves along an open immersion `j`: the
comparison `j̄_! ⟶ j̄_*` of pro-étale sheaves along the base change `j̄ : Ū ⟶ X̄`, which is
compatible with the Weil structures. -/
noncomputable def ProEtaleWeilSheaf.extensionByZeroToLowerStar (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    ProEtaleWeilSheaf.extensionByZero k₀ l j ⟶ ProEtaleWeilSheaf.lowerStar k₀ l j :=
  IsoAlgebra.mapOfNatIsoHom
    (ProEtale.adicOpenImmersionLowerShriekToLowerStar l
      (Scheme.Hom.geometricFiberMap j (comp_over j _)))
    (ProEtale.adicOpenImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso l j
      (comp_over j _))

namespace WeilSheaf

-- TODO(unify): lemma-boundary-stalk--1
/-- The *ordinary* sheaf direct image `j_*` along a quasi-compact open immersion `j` into a
`k₀`-scheme locally of finite type: the pushforward `WeilSheaf.lowerStar j`. Its stalks at the
missing points are the inertia invariants. -/
noncomputable abbrev directImage (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    WeilSheaf k₀ l U ⥤ WeilSheaf k₀ l X :=
  lowerStar j

-- TODO(unify): lemma-boundary-stalk--1
-- TODO: the isomorphism `higherDirectImage j 0 ≅ directImage j` (`R⁰j_* = j_*`), from
-- `H⁰ ∘ Rf_* ∘ single 0 ≅ f_*` for pro-étale Weil sheaves along an arbitrary `f`.
/-- The higher direct image `Rⁱj_*` along a quasi-compact open immersion `j`: the higher direct
image `WeilSheaf.higherLowerStar j i`, the cohomology sheaf `𝓗ⁱ` (indexed by `ℤ`, with
`i : ℕ` coerced) of the derived pushforward `Rj_*` of a Weil sheaf placed in degree zero. -/
noncomputable abbrev higherDirectImage (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (i : ℕ) :
    WeilSheaf k₀ l U ⥤ WeilSheaf k₀ l X :=
  higherLowerStar j i

omit [Fact (ringChar k₀ ≠ l)] in
/-- The extension by zero of a constructible sheaf along a quasi-compact open immersion is
constructible: locally on `X̄`, the strata of `Ū`, together with the closed complement of `Ū`,
on which `j̄_! F` vanishes, stratify `X̄`
(`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.openImmersionLowerShriek`). Without
quasi-compactness of `j` this fails: near a boundary point `Ū` may need infinitely many
strata. -/
theorem isAdicConstructibleSheaf_extensionByZero (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] (F : ProEtaleWeilSheaf k₀ l U)
    (hF : WeilSheaf.objectProperty k₀ l U F) :
    WeilSheaf.objectProperty k₀ l X ((ProEtaleWeilSheaf.extensionByZero k₀ l j).obj F) :=
  ProEtale.IsAdicConstructibleSheaf.openImmersionLowerShriek
    (Scheme.Hom.geometricFiberMap j (comp_over j _)) hF

-- TODO(unify): proposition-extension-zero-restriction-closed-subscheme
/-- Extension by zero `j_!` of Weil sheaves along a quasi-compact open immersion `j`: the
extension by zero along the base change `j̄ : Ū ⟶ X̄`, with the transported Weil structure. -/
noncomputable def extensionByZero (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    WeilSheaf k₀ l U ⥤ WeilSheaf k₀ l X :=
  (WeilSheaf.objectProperty k₀ l U).liftFullSubcategory (WeilSheaf.objectProperty k₀ l X)
    (ProEtaleWeilSheaf.extensionByZero k₀ l j) (isAdicConstructibleSheaf_extensionByZero j)

section ExtensionByZero

variable (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]

@[simp]
lemma extensionByZero_obj_obj_carrier (F : WeilSheaf k₀ l U) :
    ((extensionByZero j).obj F).obj.carrier =
      (Scheme.Hom.geometricFiberMap j (comp_over j _))_!ᵃ[l].obj F.obj.carrier :=
  rfl

@[simp]
lemma extensionByZero_obj_obj_str (F : WeilSheaf k₀ l U) :
    ((extensionByZero j).obj F).obj.str =
      (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l j
          (comp_over j _)).app F.obj.carrier ≪≫
        (Scheme.Hom.geometricFiberMap j (comp_over j _))_!ᵃ[l].mapIso F.obj.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ F.obj

@[simp]
lemma extensionByZero_map_hom_hom_f {F G : WeilSheaf k₀ l U} (α : F ⟶ G) :
    ((extensionByZero j).map α).hom.hom.f =
      (Scheme.Hom.geometricFiberMap j (comp_over j _))_!ᵃ[l].map α.hom.hom.f :=
  rfl

-- TODO(unify): proposition-extension-zero-restriction-closed-subscheme
omit [QuasiCompact j] in
instance : (ProEtaleWeilSheaf.extensionByZero k₀ l j).Additive :=
  IsoAlgebra.additive_mapOfNatIso _

omit [QuasiCompact j] in
instance : PreservesFiniteLimits (ProEtaleWeilSheaf.extensionByZero k₀ l j) :=
  IsoAlgebra.preservesFiniteLimits_mapOfNatIso _

omit [QuasiCompact j] in
instance : PreservesFiniteColimits (ProEtaleWeilSheaf.extensionByZero k₀ l j) :=
  IsoAlgebra.preservesFiniteColimits_mapOfNatIso _

instance : (extensionByZero (k₀ := k₀) (l := l) j).Additive :=
  ObjectProperty.liftFullSubcategory_additive _ _ _ _

end ExtensionByZero

-- TODO(unify): proposition-extension-zero-restriction-closed-subscheme
/--
The canonical map `j_! ⟶ j_*`, whose cokernel is the boundary sheaf `B` supported on the
complement of `U`:

```
  j_! F ──────▶ j_* F ──────▶ B ──────▶ 0
    │             │
    │ j_! α       │ j_* α
    ▼             ▼
  j_! G ──────▶ j_* G
```

Its components are those of the comparison `ProEtale.openImmersionLowerShriekToLowerStar` along
the base change `j̄ : Ū ⟶ X̄`.
-/
noncomputable def extensionByZeroToDirectImage (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    extensionByZero (k₀ := k₀) (l := l) j ⟶ directImage j :=
  ObjectProperty.liftFullSubcategoryMap _ _ (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l j)
    _ _

@[simp]
lemma extensionByZeroToDirectImage_app_hom_hom_f (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l U) :
    ((extensionByZeroToDirectImage j).app F).hom.hom.f =
      (ProEtale.adicOpenImmersionLowerShriekToLowerStar l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).app F.obj.carrier :=
  rfl

-- TODO(unify): proposition-extension-zero-restriction-closed-subscheme
/-- **The comparison `j_! F ⟶ j_* F` of Weil sheaves is a monomorphism**: on underlying
pro-étale sheaves it is the comparison along the base change `j̄ : Ū ⟶ X̄`, which is a
monomorphism (`AlgebraicGeometry.ProEtale.mono_adicOpenImmersionLowerShriekToLowerStar_app`). -/
instance mono_extensionByZeroToDirectImage_app (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l U) : Mono ((extensionByZeroToDirectImage j).app F) := by
  let Φ := (WeilSheaf.objectProperty k₀ l X).ι ⋙
    IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  apply Φ.mono_of_mono_map
  exact ProEtale.mono_adicOpenImmersionLowerShriekToLowerStar_app _ F.obj.carrier

end WeilSheaf

end AlgebraicGeometry
