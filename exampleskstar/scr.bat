@echo off
for %%a in (*.netdecomp) do (
echo %%a
"D:\University work - Year 3\IP\PenroseMod\dist\build\Penrose\Penrose" "Comp_NFA_FP" "%%a" "5"
echo ****************************************
)