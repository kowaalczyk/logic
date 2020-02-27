# Logic

Lab & assignment descriptions are available [here](https://lclem.github.io/logic_course/).


## Running labs

```
stack run labXX
```


## Adding new labs

1. Copy directory labXX to the project root
2. Go to labXX directory, run `cabal init`
3. Replace:
    - `LabXX` module with `Main` module in `labXX/labXX.hs`
    - remove `license-file` key from `labXX/labXX.cabal`
4. Add `labXX` to `packages` in `stack.yaml`
5. Check if it works: `stack build`
