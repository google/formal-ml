/-
Copyright 2020 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
 -/

import data.set.disjointed data.set.countable
import data.set.lattice data.set.finite
import formal_ml.nat



/-
  Although the entire repo is unapologetically classical, these results are very
  directly classical.
-/
noncomputable def classical_set (T:Type*) (S:set T):(@decidable_pred T S) :=
  λ t, classical.prop_decidable (S t)


noncomputable def classical.decidable_pred {β:Type*} (P:β → Prop):decidable_pred P:=
  (λ b:β, classical.prop_decidable (P b))


noncomputable def classical.decidable_eq (β:Type*):decidable_eq β:=
  (λ b c:β, classical.prop_decidable (b=c))


