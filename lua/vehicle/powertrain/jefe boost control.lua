-- This Source Code Form is subject to the terms of the bCDDL, v. 1.1.
-- If a copy of the bCDDL was not distributed with this
-- file, You can obtain one at http://beamng.com/bCDDL-1.1.txt

local M = {}

local AlsTable = {}
AlsTable.ALSActive = false
AlsTable.ALSTime = 2
AlsTable.tick = 0
AlsTable.engineLoadBuffer = {}
AlsTable.prevEngineLoad = 0
AlsTable.count = 1
AlsTable.instantEngineLoadDrop = 0
AlsTable.ALSNeed = false
AlsTable.ALS_RPM = 4000
AlsTable.ALSThrottle = 0
AlsTable.normalInstantAfterFireCoef = 0
AlsTable.normalSustainedAfterFireCoef = 0
AlsTable.normalSustainedAfterFireTime = 0
AlsTable.ALSInstantAfterFireCoef = 100
AlsTable.ALSSustainedAfterFireCoef = 100
AlsTable.ALSSustainedAfterFireTime = 5
AlsTable.ALS = false
AlsTable.ALSExhaustPower = 1
AlsTable.ALSPressure = 0
AlsTable.ALSInstantLoadDrop = 1
AlsTable.ALSTemp = 0
AlsTable.decreaseALSTemp = false
AlsTable.gearCount = 6
AlsTable.prevTurboAV = 0
AlsTable.turboNormalization = false
AlsTable.boostByGear = false
AlsTable.twoStepLaunchControl = nil
AlsTable.torqueOffTolerance = 10

local floor = math.floor
local sqrt = math.sqrt
local max = math.max
local min = math.min

local rpmToAV = 0.10471971768
local avToRPM = 9.5493
local invPascalToPSI = 0.00014503773773
local psiToPascal = 6894.757293178
local mpsToMph = 2.23694

M.isExisting = true

local assignedEngine = nil
local forcedInductionInfoStream = {
  rpm = 0,
  coef = 1,
  boost = 0,
  maxBoost = 0,
  exhaustPower = 0,
  friction = 0,
  backpressure = 0,
  bovEngaged = 0,
  wastegateFactor = 0,
  turboTemp = 0
}

--Turbo related stuff
local turboRPM = 0
local curTurboAV = 0
local maxTurboAV = 1
local invMaxTurboAV = 1
local invTurboInertia = 0
local turboInertiaFactor = 1
local turboPressure = 0
local turboPressureRaw = 0
local maxTurboPressure = {}
local exhaustPower = 0
local maxExhaustPower = 1
local backPressureCoef = 0
local frictionCoef = 0
local turboWhineLoop = nil
local turboHissLoop = nil
local turboWhinePitchPerAV = 0
local turboWhineVolumePerAV = 0
local  VolumePerPascal = 0
local backPressure = 0
local damaged = false
local wastegateTargetBoost = 0

-- Wastegate
local wastegateStart = nil
local wastegateLimit = nil
local wastegateFactor = 1
local wastegateRange = nil
local maxWastegateStart = 0
local maxWastegateLimit = 0
local maxWastegateRange = 1
local wastegatePCoef = 0
local wastegateICoef = 0
local wastegateDCoef = 0
local wastegateIntegral = 0
local lastBoostError = 0
local wastegateTargetBoost = 0
local wastegateStartPerGear = 0
local wastegateRangePerGear = 0

-- blow off valve
local bovEnabled = true
local bovEngaged = false
local bovRequested = false
local lastBOVValue = false
local lastEngineLoad = 0
local bovOpenChangeThreshold = 0
local bovOpenThreshold = 0
local bovSoundVolumeCoef = 1
local bovSoundPressureCoef = 1
local bovTimer = 0
local ignitionCutSmoother = nil
local needsBov = false
local bovSound = nil
local flutterSoundVolumeCoef = 1
local flutterSoundPressureCoef = 1
local flutterSound = nil

local invEngMaxAV = 0

local turbo = nil
local pressureSmoother = nil
local wastegateSmoother = nil
local electricsRPMName = nil
local electricsSpinName = nil
local electricsSpinCoef = nil
local electricsSpinValue = nil

local turboDamageThresholdTemperature = 0

local function updateSounds(dt)
  if turboWhineLoop then
    local ALSgear = electrics.values.gearIndex >= 1 and (#AlsTable.ALSPressure > 1 and electrics.values.gearIndex or 1) or 1
    local spindlePitch = 0
    local spindleVolume = 0
    local hissVolume = 0
    if AlsTable.ALSActive then
      spindlePitch = curTurboAV * turboWhinePitchPerAV
      hissVolume = max(AlsTable.ALSPressure[ALSgear] * turboHissVolumePerPascal, 0)
      spindleVolume = curTurboAV * hissVolume * 3 * turboWhineVolumePerAV
      obj:setVolumePitch(turboHissLoop, hissVolume, 1)
      obj:setVolumePitch(turboWhineLoop, spindleVolume, spindlePitch)
    else
      if curTurboAV <= maxTurboAV / 5 then
        electrics.values.turboWhineVolumePerAV = turboWhineVolumePerAV
      end
      spindlePitch = curTurboAV * turboWhinePitchPerAV
      spindleVolume = curTurboAV * electrics.values.turboWhineVolumePerAV
      hissVolume = max(turboPressure * turboHissVolumePerPascal, 0)
      obj:setVolumePitch(turboHissLoop, hissVolume, 1)
      obj:setVolumePitch(turboWhineLoop, spindleVolume, spindlePitch)
    end
  end
end

local function updateFixedStep(dt)
  if assignedEngine.engineDisabled then
    M.updateGFX = nop
    M.updateFixedStep = nop
    electrics.values.turboRpmRatio = 0
    electrics.values.turboBoost = 0
    turboPressure = 0
    turboPressureRaw = 0
    curTurboAV = 0
    return
  end
  local ALSgear = electrics.values.gearIndex >= 1 and (#AlsTable.ALSPressure > 1 and electrics.values.gearIndex or 1) or 1
  local sButton = electrics.values.scramble + 1
  --local gear = electrics.values.gearIndex or 1
 -- local wastegateStartPerGear = wastegateStart and (wastegateStart[gear] or maxWastegateStart) or 0--maxWastegateStart[sButton]--wastegateStart and (wastegateStart[gear] or maxWastegateStart) or 0
  --local wastegateRangePerGear = wastegateRange and (wastegateRange[gear] or maxWastegateRange) or 0--maxWastegateRange[sButton]--wastegateRange and (wastegateRange[gear] or maxWastegateRange) or 0
  --wastegateFactor = bovEngaged and 0 or wastegateSmoother:getUncapped(clamp((1 - (max(turboPressureRaw - (type(wastegateStartPerGear) == "table" and wastegateStartPerGear[sButton] or wastegateStartPerGear), 0) / (type(wastegateRangePerGear) == "table" and wastegateRangePerGear[sButton] or wastegateRangePerGear))), 0, 1), dt)

  --calculate wastegate factor
  local boostError = turboPressureRaw - wastegateTargetBoost
  wastegateIntegral = clamp(wastegateIntegral + boostError * dt, -500, 500)
  local wastegateDerivative = (boostError - lastBoostError) / dt
  wastegateFactor = bovEngaged and 0 or wastegateSmoother:getUncapped(clamp((1 - (boostError * wastegatePCoef + wastegateIntegral * wastegateICoef + wastegateDerivative * wastegateDCoef)), 0, 1), dt)

  local engAV = max(1, assignedEngine.outputAV1)
  local engAvRatio = min(engAV * invEngMaxAV, 1)
  local engineRPM = floor(max(assignedEngine.outputRPM or 0, 0))

  AlsTable.rollingALS = electrics.values.rollingALS == 1
  AlsTable.ALSActive = AlsTable.ALSActive or AlsTable.rollingALS and engineRPM > 0 and ALSgear >= 1

  if AlsTable.ALSActive then
    exhaustPower = min(exhaustPower + (850000 * dt), AlsTable.ALSExhaustPower)

    if AlsTable.ALSThrottle == 0 and electrics.values.airspeed * mpsToMph <= 1 then
      electrics.values.throttle = electrics.values.throttle + 0.01
    end

    assignedEngine.instantAfterFireCoef   = AlsTable.ALSInstantAfterFireCoef
    assignedEngine.sustainedAfterFireCoef = AlsTable.ALSSustainedAfterFireCoef
    assignedEngine.sustainedAfterFireTime = AlsTable.ALSSustainedAfterFireTime
  else
  	exhaustPower = (0.1 + assignedEngine.engineLoad * 0.8) * assignedEngine.throttle * assignedEngine.throttle * engAvRatio * (turbo.turboExhaustCurve[floor(assignedEngine.outputRPM)] or 1) * maxExhaustPower * dt

	  assignedEngine.instantAfterFireCoef   = AlsTable.normalInstantAfterFireCoef
    assignedEngine.sustainedAfterFireCoef = AlsTable.normalSustainedAfterFireCoef
    assignedEngine.sustainedAfterFireTime = AlsTable.normalSustainedAfterFireTime
  end

  local friction = frictionCoef * dt --simulate some friction and stuff there
  backPressure = curTurboAV * curTurboAV * backPressureCoef * (bovEngaged and 0.4 or 1) * dt --back pressure from compressing the air
  local turboTorque = ((exhaustPower * wastegateFactor) - backPressure - friction)
  --curTurboAV = clamp((curTurboAV + dt * turboTorque * invTurboInertia), 0, maxTurboAV)
  if AlsTable.ALSActive then
    curTurboAV = min(curTurboAV + (120000 * dt), (AlsTable.invTurboPressureCurve[floor(wastegateTargetBoost * AlsTable.ALSPressureRate * invPascalToPSI)] or AlsTable.invTurboPressureCurve[AlsTable.invTurboPressureCurveCount]) * rpmToAV)
    AlsTable.timeSinceLastActivation = 0
  else
    curTurboAV = clamp((curTurboAV + dt * turboTorque * invTurboInertia), 0, maxTurboAV)
    AlsTable.timeSinceLastActivation = AlsTable.timeSinceLastActivation + dt
  end

  --Turbo Normalization (kinda) not 100% accurate when boost by speed is selected
  if AlsTable.turboNormalization and assignedEngine.instantEngineLoad >= 0.3 then
    local torqueAtSeaLevel
    if AlsTable.boostByGear then
      torqueAtSeaLevel = (AlsTable.torqueCurveAtSeaLevel[ALSgear][sButton][engineRPM] or 0) * electrics.values.throttle --Aproximation of the torque the engine would be producing if at sea level \
    else                                                                                                                --                                                                          -- this does NOT take into consideration the presence of a supercharger or a N02 System
      torqueAtSeaLevel = (AlsTable.torqueCurveAtSeaLevel[1][sButton][engineRPM] or 0) * electrics.values.throttle       --Aproximation of the torque the engine would be producing if at sea level /
    end
    local torqueDelta = max(torqueAtSeaLevel - (assignedEngine.combustionTorque <= 0 and torqueAtSeaLevel or assignedEngine.combustionTorque), 0)
    local torqueOffPerc = torqueAtSeaLevel ~= 0 and (torqueDelta * 100 / torqueAtSeaLevel) or 0
    local relativeAirDensity = obj:getRelativeAirDensity()
    if torqueOffPerc >= AlsTable.torqueOffTolerance * relativeAirDensity * relativeAirDensity * relativeAirDensity then --If the torque delta is not high enough the boost will be very unstable (+/- 0.1Bar)
      local tp = (turboPressure + (torqueOffPerc / math.sqrt(relativeAirDensity)) * psiToPascal) --Calculate the needed turbo pressure to keep the same torque as at sea level
      --turboPressure = min(pressureSmoother:getUncapped(tp, dt * 2), tp) --Smooth the result and apply it
      if AlsTable.isBoostBySpeed then
        local index
        if electrics.values.airspeed * mpsToMph <= AlsTable.boostAtSpeedCount then
          index = floor(electrics.values.airspeed * mpsToMph)
        else
          index = AlsTable.boostAtSpeedCount
        end
          curTurboAV = min(curTurboAV + (120000 * dt), (AlsTable.invTurboPressureCurve[floor(tp * invPascalToPSI)] or AlsTable.invTurboPressureCurve[AlsTable.invTurboPressureCurveCount]) * (wastegateTargetBoost / AlsTable.boostAtSpeed[sButton][index]) * rpmToAV)
      else
        curTurboAV = min(curTurboAV + (120000 * dt), (AlsTable.invTurboPressureCurve[floor(tp * invPascalToPSI)] or AlsTable.invTurboPressureCurve[AlsTable.invTurboPressureCurveCount]) * rpmToAV)
      end
    end
end


  turboRPM = curTurboAV * avToRPM

  turboPressureRaw = assignedEngine.isStalled and 0 or ((turbo.turboPressureCurve[floor(turboRPM)] * psiToPascal) or turboPressure)
  turboPressure = pressureSmoother:getUncapped(turboPressureRaw, dt / (AlsTable.timeSinceLastActivation >= 1 and 1 or (AlsTable.timeSinceLastActivation == 0 and 0.0000001 or AlsTable.timeSinceLastActivation)))
  -- --old Turbo Normalization
  -- if AlsTable.turboNormalization and assignedEngine.instantEngineLoad >= 0.3 then
  --     local torqueAtSeaLevel
  --     if AlsTable.boostByGear then
  --       torqueAtSeaLevel = (AlsTable.torqueCurveAtSeaLevel[ALSgear][sButton][engineRPM] or 0) * electrics.values.throttle --Aproximation of the torque the engine would be producing if at sea level \
  --     else                                                                                                                --                                                                          -- this does NOT take into consideration the presence of a supercharger or a N02 System
  --       torqueAtSeaLevel = (AlsTable.torqueCurveAtSeaLevel[1][sButton][engineRPM] or 0) * electrics.values.throttle       --Aproximation of the torque the engine would be producing if at sea level /
  --     end
  --     local torqueDelta = max(torqueAtSeaLevel - (assignedEngine.combustionTorque <= 0 and torqueAtSeaLevel or assignedEngine.combustionTorque), 0)
  --     local torqueOffPerc = torqueAtSeaLevel ~= 0 and (torqueDelta * 100 / torqueAtSeaLevel) or 0
  --     local relativeAirDensity = obj:getRelativeAirDensity()
  --     if torqueOffPerc >= AlsTable.torqueOffTolerance * relativeAirDensity * relativeAirDensity * relativeAirDensity then --If the torque delta is not high enough the boost will be very unstable (+/- 0.1Bar)
  --       local tp = (turboPressure + (torqueOffPerc / math.sqrt(relativeAirDensity)) * psiToPascal) --Calculate the needed turbo pressure to keep the same torque as at sea level
  --       turboPressure = min(pressureSmoother:getUncapped(tp, dt * 2), tp) --Smooth the result and apply it
  --     end
  -- end

  -- 1 psi = 6% more power
  -- 1 pascal = 0.00087% more power
  assignedEngine.forcedInductionCoef = assignedEngine.forcedInductionCoef * (1 + 0.0000087 * turboPressure * (turbo.turboEfficiencyCurve[engineRPM] or 0))
end

local function updateGFX(dt)
  --Some verification stuff
  if assignedEngine.engineDisabled then
    M.updateGFX = nop
    M.updateFixedStep = nop
    electrics.values.turboRpmRatio = 0
    electrics.values.turboBoost = 0
    turboPressure = 0
    turboPressureRaw = 0
    curTurboAV = 0
    return
  end

  local sButton = electrics.values.scramble + 1
  local ALSgear = electrics.values.gearIndex >= 1 and (#AlsTable.ALSPressure > 1 and electrics.values.gearIndex or 1) or 1

  local gear = electrics.values.gearIndex or 1
  wastegateStartPerGear = wastegateStart[gear] or maxWastegateStart
  wastegateRangePerGear = wastegateRange[gear] or maxWastegateRange
  if AlsTable.isBoostBySpeed then
    if electrics.values.airspeed * mpsToMph <= AlsTable.boostAtSpeedCount then
      wastegateTargetBoost = AlsTable.boostAtSpeed[sButton][floor(electrics.values.airspeed * mpsToMph)]
    else
      wastegateTargetBoost = AlsTable.boostAtSpeed[sButton][AlsTable.boostAtSpeedCount]
    end
  else
    wastegateTargetBoost = wastegateStartPerGear[sButton] + wastegateRangePerGear[sButton] * 0.5
  end

  if AlsTable.count > 600000 then
    AlsTable.count = 1
  end
  AlsTable.engineLoadBuffer[AlsTable.count] = assignedEngine.engineLoad
  AlsTable.prevEngineLoad = (AlsTable.engineLoadBuffer[AlsTable.count - 1] or 0)
  AlsTable.count = AlsTable.count + 1
  -- if #AlsTable.engineLoadBuffer >= 600000 then
    -- AlsTable.engineLoadBuffer = {}
    -- AlsTable.engineLoadBuffer[1] = AlsTable.prevEngineLoad
  -- end

  AlsTable.twoStepLaunchControl = require("controller/twoStepLaunch")
  AlsTable.twoStepRpm = AlsTable.twoStepLaunchControl:serialize().rpm
  electrics.values.twoStepState = AlsTable.twoStepLaunchControl:serialize().state

  AlsTable.instantEngineLoadDrop = AlsTable.prevEngineLoad - assignedEngine.instantEngineLoad

  if ((AlsTable.instantEngineLoadDrop > AlsTable.ALSInstantLoadDrop and electrics.values.airspeed * mpsToMph >= 3) or (assignedEngine.outputRPM >= AlsTable.twoStepRpm and electrics.values.twoStepState == "armed") or (assignedEngine.outputRPM <= AlsTable.ALS_RPM and assignedEngine.throttle >= 0.9 and electrics.values.airspeed * mpsToMph >= 2) or (assignedEngine.outputRPM >= assignedEngine.maxRPM and electrics.values.airspeed * mpsToMph <= 1)) and AlsTable.ALS and (electrics.values.ALS_toggle == 1) and (not assignedEngine.engineDisabled and assignedEngine.outputRPM > 10) then --and electrics.values.throttle <= 0.2 then--lastEngineLoad - electrics.values.engineLoad >= 0.2 then
   	AlsTable.ALSNeed = true
    AlsTable.ALSThrottle = electrics.values.throttle
  end

  if electrics.values.throttle > 0 and not (assignedEngine.outputRPM >= assignedEngine.maxRPM - 200 and electrics.values.airspeed * mpsToMph <= 1 and electrics.values.throttle >= 1) and electrics.values.brake <= 0.2 and AlsTable.ALSActive then
    if not electrics.values.ALStwoStep and not assignedEngine.outputRPM >= AlsTable.twoStepRpm then
      AlsTable.tick = 0
      AlsTable.ALSActive = false
      AlsTable.ALSNeed = false
      AlsTable.decreaseALSTemp = true
    end
  end

  electrics.values.ALStwoStep = assignedEngine.outputRPM >= AlsTable.twoStepRpm - (2 * electrics.values.revLimiterRPMDrop) and electrics.values.twoStepState == "armed"
  electrics.values.doingBurnout = electrics.values.brake >= 0.2 and electrics.values.throttle >= 0.2 and electrics.values.airspeed <= 2 and electrics.values.airspeed * mpsToMph >= 1
  electrics.values.ALSRevlimiter = assignedEngine.outputRPM >= (assignedEngine.maxRPM - 2 * electrics.values.revLimiterRPMDrop) and electrics.values.airspeed * mpsToMph <= 2

  if AlsTable.ALSNeed and (electrics.values.throttle <= 0 or electrics.values.airspeed * mpsToMph <= 0.1 and (electrics.values.doingBurnout or electrics.values.ALSRevlimiter or electrics.values.ALStwoStep) or assignedEngine.outputRPM >= assignedEngine.maxRPM - 200 and electrics.values.airspeed * mpsToMph <= 1 and electrics.values.throttle >= 1) then
    AlsTable.tick = AlsTable.tick + dt
    AlsTable.ALSTemp = math.abs(AlsTable.ALSTemp) + ((AlsTable.ALSPressure[ALSgear] + AlsTable.ALSExhaustPower) / 10000) * dt
    if AlsTable.tick >= AlsTable.ALSTime then
      AlsTable.tick = 0
  	  if (not electrics.values.doingBurnout) and (not electrics.values.ALSRevlimiter) and (not electrics.values.ALStwoStep) then
        AlsTable.ALSActive = false
        AlsTable.ALSNeed = false
    	  AlsTable.decreaseALSTemp = true
        electrics.values.CanBOV = true
        obj:setVolumePitchCT(bovSound, min(max((AlsTable.ALSPressure[ALSgear] <= 1400 and 0 or AlsTable.ALSPressure[ALSgear]) / maxTurboPressure[sButton], 0), 1) * bovSoundPressureCoef * 5, 1, bovSoundVolumeCoef, 0)
    	  obj:playSFX(bovSound)
  	  end
    elseif not AlsTable.ALSActive then
      AlsTable.ALSActive = true
      AlsTable.ALSNeed = true
	    electrics.values.CanBOV = false
    end
  else
      AlsTable.tick = 0
      AlsTable.ALSActive = false
      AlsTable.decreaseALSTemp = true
      electrics.values.CanBOV = true
  end
  if AlsTable.decreaseALSTemp then
  	AlsTable.ALSTemp = AlsTable.ALSTemp - ((AlsTable.ALSPressure[ALSgear] + AlsTable.ALSExhaustPower) / 9000) * dt
    electrics.values.turboWhineVolumePerAV = max(turboWhineVolumePerAV - 0.001 * dt, 0)
    if AlsTable.ALSTemp <= 0 then
      AlsTable.decreaseALSTemp = false
      electrics.values.turboWhineVolumePerAV = 0
      AlsTable.ALSTemp = 0
    end
  end

  local turboTemp = AlsTable.ALSTemp + assignedEngine.thermals.exhaustTemperature + (assignedEngine.thermals.coolantTemperature or 0) + assignedEngine.thermals.oilTemperature
  --calculate turbo damage using our turbo temp
  if turboTemp > turboDamageThresholdTemperature then
    frictionCoef = frictionCoef * (1 + (turboTemp - turboDamageThresholdTemperature) * 0.001 * dt)
    damageTracker.setDamage("engine", "turbochargerHot", true)
  else
    damageTracker.setDamage("engine", "turbochargerHot", false)
  end

  --open the BOV if we have very little load or if the engine load drops significantly
  local loadLow = assignedEngine.instantEngineLoad < bovOpenThreshold or assignedEngine.requestedThrottle <= 0
  local highLoadDrop = (lastEngineLoad - assignedEngine.instantEngineLoad) > bovOpenChangeThreshold
  local notInRevLimiter = assignedEngine.revLimiterWasActiveTimer > 0.1
  local ignitionNotCut = ignitionCutSmoother:getUncapped(assignedEngine.ignitionCutTime > 0 and 1 or 0, dt) <= 0
  local bovRequested = needsBov and (loadLow or highLoadDrop) and notInRevLimiter and ignitionNotCut
  bovEngaged = bovEnabled and bovRequested
  bovTimer = max(bovTimer - dt, 0)

  if bovRequested and needsBov and not lastBOVValue and bovTimer <= 0 and electrics.values.CanBOV and not AlsTable.ALSActive then
    if bovEnabled then
      local relativePressure = min(max(turboPressure / maxTurboPressure[sButton], 0), 1)
      local bovVolume = relativePressure * bovSoundPressureCoef
      obj:setVolumePitchCT(bovSound, bovVolume, 1, bovSoundVolumeCoef, 0)
      obj:playSFX(bovSound)
    else
      local relativePressure = min(max(turboPressure / maxTurboPressure[sButton], 0), 1)
      local flutterVolume = relativePressure * flutterSoundPressureCoef
      obj:setVolumePitchCT(flutterSound, flutterVolume, 1, flutterSoundVolumeCoef, 0)
      obj:playSFX(flutterSound)
    end
    bovTimer = 0.5
  end

  if bovRequested and electrics.values.CanBOV then --if the BOV is supposed to be open and we have positive pressure, we don't actually have any pressure ;)
    turboPressure = 0
    pressureSmoother:getUncapped(turboPressure, dt)
  elseif lastBOVValue then
    if bovSound then
      obj:stopSFX(bovSound)
    end
    if flutterSound then
      obj:stopSFX(flutterSound)
    end
  end

  electrics.values[electricsRPMName] = turboRPM
  electricsSpinValue = electricsSpinValue + turboRPM * dt
  electrics.values[electricsSpinName] = (electricsSpinValue * electricsSpinCoef) % 360
  -- Update sounds
  electrics.values.turboRpmRatio = curTurboAV * invMaxTurboAV * 580
  electrics.values.turboBoost = turboPressure * invPascalToPSI

  lastEngineLoad = assignedEngine.instantEngineLoad
  lastBOVValue = bovRequested

  -- Update streams
  if streams.willSend("forcedInductionInfo") then
    forcedInductionInfoStream.rpm = curTurboAV * avToRPM
    forcedInductionInfoStream.coef = assignedEngine.forcedInductionCoef
    forcedInductionInfoStream.boost = turboPressure * 0.001
    forcedInductionInfoStream.exhaustPower = exhaustPower / dt
    forcedInductionInfoStream.backpressure = backPressure / dt
    forcedInductionInfoStream.bovEngaged = (bovEngaged and 1 or 0) * 10
    forcedInductionInfoStream.wastegateFactor = wastegateFactor * 10
    forcedInductionInfoStream.turboTemp = turboTemp

    gui.send("forcedInductionInfo", forcedInductionInfoStream)
  end
end

local function reset()
  AlsTable.ALSInstantAfterFireCoef   = 100
  AlsTable.ALSSustainedAfterFireCoef = 100
  AlsTable.ALSSustainedAfterFireTime = 5
  electrics.values.CanBOV = true
  electrics.values.scramble = 0

  curTurboAV = 0
  turboPressure = 0
  turboPressureRaw = 0
  bovEngaged = false
  lastBOVValue = true
  lastEngineLoad = 0
  wastegateFactor = 1
  bovTimer = 0
  wastegateIntegral = 0
  lastBoostError = 0
  wastegateTargetBoost = 0
  wastegateStartPerGear = 0
  wastegateRangePerGear = 0
  electricsSpinValue = 0

  AlsTable.ALSActive = false
  AlsTable.engineLoadBuffer = {}
  AlsTable.prevEngineLoad = 0
  AlsTable.count = 1
  AlsTable.instantEngineLoadDrop = 0
  AlsTable.ALSThrottle = 0
  AlsTable.ALSNeed = false
  AlsTable.ALSTemp = 0
  damaged = false
  AlsTable.decreaseALSTemp = false

  frictionCoef = turbo.frictionCoef or 0.01

  pressureSmoother:reset()
  wastegateSmoother:reset()
  ignitionCutSmoother:reset()

  damageTracker.setDamage("engine", "turbochargerHot", false)
  AlsTable.timeSinceLastActivation = AlsTable.ALSTime
end

local function init(device, jbeamData)
  turbo = jbeamData
  if turbo == nil then
    M.turboUpdate = nop
    return
  end
  local rpmToAV = 0.10471971768
  local avToRPM = 9.5493
  local invPascalToPSI = 0.00014503773773
  local psiToPascal = 6894.757293178

  assignedEngine = device

  curTurboAV = 0
  turboPressure = 0
  turboPressureRaw = 0
  bovEngaged = false
  lastBOVValue = true
  lastEngineLoad = 0
  wastegateFactor = 1
  bovTimer = 0
  wastegateIntegral = 0
  lastBoostError = 0
  wastegateTargetBoost = 0
  wastegateStartPerGear = 0
  wastegateRangePerGear = 0

  maxTurboAV = 1
  electrics.values.scramble = 0
  electrics.values.scramblePressure = (turbo.scramblePressure or 0) * psiToPascal

  -- add the turbo pressure curve
  -- define y PSI at x RPM
  local pressurePSIcount = #turbo.pressurePSI
  local tpoints = table.new(pressurePSIcount, 0)
  if turbo.pressurePSI then
    for i = 1, pressurePSIcount do
      local point = turbo.pressurePSI[i]
      tpoints[i] = {point[1], point[2]}
      --Get max turbine rpm
      maxTurboAV = max(point[1] * rpmToAV, maxTurboAV)
    end
  else
    log("E", "Turbo", "No turbocharger.pressurePSI table found!")
    return
  end
  turbo.turboPressureCurve = createCurve(tpoints, true)
  -- add the turbo exhaust curve
  -- simulate pressure factor going between the exhasut and the turbine
  --
  -- add the turbo efficiency curve
  -- simulate power coef per engine RPM
  -- Eg: Small turbos will be more efficient on engine low rpm than high rpm and vice versa
  local engineDefcount = #turbo.engineDef
  local tepoints = table.new(engineDefcount, 0)
  local tipoints = table.new(engineDefcount, 0)
  if turbo.engineDef then
    for i = 1, engineDefcount do
      local point = turbo.engineDef[i]
      tepoints[i] = {point[1], point[2]}
      tipoints[i] = {point[1], min(point[3], 1)}
    end
  else
    log("E", "Turbo", "No turbocharger.engineDef curve found!")
    return
  end

  turbo.turboExhaustCurve = createCurve(tipoints)
  turbo.turboEfficiencyCurve = createCurve(tepoints)

  turboInertiaFactor = (turbo.inertia * 100) or 1

  wastegateStart = {}
  wastegateLimit = {}
  wastegateRange = {}
  AlsTable.torqueCurveAtSeaLevel = {}
  local turboCoefs = {}
  local maxGear = v.data.gearbox.gearRatios and #v.data.gearbox.gearRatios - 2 or AlsTable.gearCount
  if(type(turbo.wastegateStart) == "table") then
	  loopLimit = maxGear
    AlsTable.boostByGear = true
  else
	  loopLimit = 1
  end

  for i = 1,  loopLimit do
    wastegateStart[i] = {}
	  wastegateLimit[i] = {}
	  wastegateRange[i] = {}
    AlsTable.torqueCurveAtSeaLevel[i] = {}
    turboCoefs[i] = {}
    for j = 1, 2 do
      wastegateStart[i][j] = 0
	    wastegateLimit[i][j] = 0
	    wastegateRange[i][j] = 0
      AlsTable.torqueCurveAtSeaLevel[i][j] = {}
      turboCoefs[i][j] = {}
    end
  end

  maxWastegateStart = {}
  maxWastegateLimit = {}
  if type(turbo.wastegateStart) == "table" then
    for k, v in pairs(turbo.wastegateStart) do
      if k <= maxGear then
        --scramble pressure already in pascal
        v = v * psiToPascal--V to Pascal
        --wastegateStart[k] = {}
        wastegateStart[k][1] = v
        wastegateStart[k][2] = v + electrics.values.scramblePressure

        if(k == 6) then
          for i = 6, loopLimit do
            wastegateStart[i][1] = wastegateStart[6][1]
            wastegateStart[i][2] = (wastegateStart[i][1] + (electrics.values.scramblePressure))
          end
        end
      end
    end

    for i = 1, table.getn(wastegateStart) do
      if wastegateStart[i][1] > (maxWastegateStart[1] or -1) and i <= maxGear then
        maxWastegateStart[1] = wastegateStart[i][1]
      end
      if wastegateStart[i][2] > (maxWastegateStart[2] or -1) and i <= maxGear then
        maxWastegateStart[2] = wastegateStart[i][2]
      end
    end

  else
    --wastegateStart[1] = {}

    wastegateStart[1][1] = (turbo.wastegateStart or 0) * psiToPascal
    maxWastegateStart[1] = wastegateStart[1][1]

	  wastegateStart[1][2] = (turbo.wastegateStart or 0) * psiToPascal + electrics.values.scramblePressure
    maxWastegateStart[2] = wastegateStart[1][2]
  end

  if type(turbo.wastegateLimit) == "table" then
    local tmp = -1
    for k, v in pairs(turbo.wastegateLimit) do
        --wastegateLimit[k] = {}
      if k <= maxGear then
	      wastegateLimit[k][1] = v * psiToPascal
	      tmp = wastegateLimit[k][1]
        if tmp > (maxWastegateLimit[1] or -1)  and k <= maxGear then
          maxWastegateLimit[1] = tmp
        end

	      wastegateLimit[k][2] = (v + (electrics.values.scramblePressure * invPascalToPSI)) * psiToPascal

        tmp = wastegateLimit[k][2] + (electrics.values.scramblePressure * invPascalToPSI)
        if tmp > (maxWastegateLimit[2] or -1) and k <= maxGear then
          maxWastegateLimit[2] = tmp
        end

        if(k == 6) then
  	  	  for i = 6, loopLimit do
            wastegateLimit[i][1] = wastegateLimit[6][1]
  	  	    wastegateLimit[i][2] = wastegateLimit[i][1] + electrics.values.scramblePressure
  	  	  end
        end
      end
    end
  else
    --wastegateLimit[1] = {}

    wastegateLimit[1][1] = (turbo.wastegateLimit or 0) * psiToPascal
    maxWastegateLimit[1] = wastegateLimit[1][1]

  	wastegateLimit[1][2] = ((turbo.wastegateLimit or 0)) * psiToPascal + electrics.values.scramblePressure
    maxWastegateLimit[2] = wastegateLimit[1][2]
  end

  maxWastegateRange = {}
  for k, v in pairs(wastegateStart) do
    --wastegateRange[k] = {}
		local start = v[1]
		local limit = wastegateLimit[k][1] or maxWastegateLimit[1]
		wastegateRange[k][1] = limit - start
		maxWastegateRange[1] = wastegateRange[k][1]

		start = v[2]
		limit = wastegateLimit[k][2] or maxWastegateLimit[2]
		wastegateRange[k][2] = limit - start
		maxWastegateRange[2] = wastegateRange[k][2]
  end

  AlsTable.ALSTime = turbo.ALSTime or 2
  AlsTable.timeSinceLastActivation = AlsTable.ALSTime
  AlsTable.ALS_RPM = turbo.ALS_RPM or 0
  AlsTable.ALS = turbo.ALS or false
  AlsTable.ALSExhaustPower = turbo.ALSExhaustPower or 1
  AlsTable.gearCount = v.data.gearbox.gearRatios and #v.data.gearbox.gearRatios - 2 or AlsTable.gearCount
  AlsTable.ALSPressureRate = turbo.ALSPressure / 100
  AlsTable.ALSPressure = {}
  for k, v in pairs(wastegateStart[1]) do
    local value = ((type(turbo.wastegateStart) == "table" and wastegateLimit[k][1] or wastegateLimit[1][1]) or 0) * turbo.ALSPressure / 100

    AlsTable.ALSPressure[k] = value
    if AlsTable.ALSPressure[k] > (maxALSPressure or -1) then
  	  maxALSPressure = AlsTable.ALSPressure[k]
    end
    if AlsTable.ALSPressure[k + 1] then
    	if AlsTable.ALSPressure[k] > AlsTable.ALSPressure[k + 1] then
    	  AlsTable.ALSPressure[k + 1] = AlsTable.ALSPressure[k]
    	end
    end
  end

  if #AlsTable.ALSPressure or 1 < AlsTable.gearCount then
    for i = #AlsTable.ALSPressure, AlsTable.gearCount do
      AlsTable.ALSPressure[i] = maxALSPressure
    end
  end

  AlsTable.isBoostBySpeed = turbo.isBoostBySpeed or false
  if AlsTable.isBoostBySpeed then
    local points = turbo.boostAtSpeed
    if points == nil then
      log("E", "Turbo", "No Boost At Speed curve found!!")
      return
    end

    local boostAtSpeed = {{}, {}}
    for i = 1, #points do
      boostAtSpeed[1][i] = {turbo.boostAtSpeed[i][1], turbo.boostAtSpeed[i][2] * psiToPascal}
      boostAtSpeed[2][i] = {turbo.boostAtSpeed[i][1], turbo.boostAtSpeed[i][2] * psiToPascal + electrics.values.scramblePressure}
    end
    AlsTable.boostAtSpeed = {createCurve(boostAtSpeed[1]), createCurve(boostAtSpeed[2])}
    AlsTable.boostAtSpeedCount = #(AlsTable.boostAtSpeed[1])
  end

  local invTurboPressureCurvePoints = table.new(pressurePSIcount, 0)
  for i = 1, pressurePSIcount do
    local point = turbo.pressurePSI[i]
    invTurboPressureCurvePoints[i] = {point[2], point[1]}
  end
  local invTurboPressureCurve = createCurve(invTurboPressureCurvePoints)
  AlsTable.invTurboPressureCurve = invTurboPressureCurve
  AlsTable.invTurboPressureCurveCount = #AlsTable.invTurboPressureCurve

  AlsTable.ALSInstantLoadDrop = turbo.ALSInstantLoadDrop or 1
  electrics.values.ALS_toggle = 0
  AlsTable.decreaseALSTemp = false

  maxExhaustPower = turbo.maxExhaustPower or 1

  backPressureCoef = turbo.backPressureCoef or 0.0005
  frictionCoef = turbo.frictionCoef or 0.01

  turboDamageThresholdTemperature = turbo.damageThresholdTemperature or 1000

  wastegatePCoef = turbo.wastegatePCoef or 0.0001
  wastegateICoef = turbo.wastegateICoef or 0.0015
  wastegateDCoef = turbo.wastegateDCoef or 0

  electricsRPMName = turbo.electricsRPMName or "turboRPM"
  electricsSpinName = turbo.electricsSpinName or "turboSpin"
  electricsSpinCoef = turbo.electricsSpinCoef or 0.1
  electricsSpinValue = 0

  --optimizations:
  invMaxTurboAV = 1 / maxTurboAV
  invEngMaxAV = 1 / ((assignedEngine.maxRPM or 8000) * rpmToAV)
  invTurboInertia = 1 / (0.000003 * turboInertiaFactor * 2.5)
  pressureSmoother = newTemporalSmoothing(100 * psiToPascal, (turbo.pressureRatePSI or 30) * psiToPascal)
  wastegateSmoother = newTemporalSmoothing(50, 50)
  ignitionCutSmoother = newTemporalSmoothing(1, 10)
  bovEnabled = (turbo.bovEnabled == nil or turbo.bovEnabled)
  bovOpenThreshold = turbo.bovOpenThreshold or 0.05
  bovOpenChangeThreshold = turbo.bovOpenChangeThreshold or 0.3
  needsBov = assignedEngine.requiredEnergyType ~= "diesel"
  --maxTurboPressure = maxWastegateStart * invPascalToPSI * (1 + (maxWastegateRange * invPascalToPSI) * 0.01) * psiToPascal
  maxTurboPressure[1] = maxWastegateStart[1] * invPascalToPSI * (1 + (maxWastegateRange[1] * invPascalToPSI) * 0.01) * psiToPascal
  maxTurboPressure[2] = maxWastegateStart[2] * invPascalToPSI * (1 + (maxWastegateRange[2] * invPascalToPSI) * 0.01) * psiToPascal

  forcedInductionInfoStream.friction = frictionCoef
  forcedInductionInfoStream.maxBoost = maxWastegateLimit[2] * 0.001

  damageTracker.setDamage("engine", "turbochargerHot", false)

  AlsTable.normalInstantAfterFireCoef   = assignedEngine.instantAfterFireCoef   or 0
  AlsTable.normalSustainedAfterFireCoef = assignedEngine.sustainedAfterFireCoef or 0
  AlsTable.normalSustainedAfterFireTime = assignedEngine.sustainedAfterFireTime or 2.5
  AlsTable.ALSInstantAfterFireCoef   = 100
  AlsTable.ALSSustainedAfterFireCoef = 100
  AlsTable.ALSSustainedAfterFireTime = 5
  electrics.values.CanBOV = true

  AlsTable.twoStepLaunchControl = require("controller/twoStepLaunch")
  AlsTable.twoStepRpm = AlsTable.twoStepLaunchControl:serialize().rpm

  electrics.values.revLimiterRPMDrop = (assignedEngine.revLimiterAVDrop or 5) * avToRPM
  if assignedEngine.revLimiterType == "timeBased" then
    electrics.values.revLimiterRPMDrop = (assignedEngine.revLimiterMaxAVDrop or 5) * avToRPM
  end
  v.data.turbocharger.wastegateStart = maxWastegateStart[2] * invPascalToPSI

  --Turbo Normalization Init
  AlsTable.turboNormalization = turbo.turboNormalization or false
  if AlsTable.turboNormalization then
    AlsTable.torqueOffTolerance = turbo.torqueOffTolerance or 10
    for i = 1, loopLimit do
      for j = 1, 2 do
        turboCoefs[i][j] = getTorqueCoefs(i, j) --Get the turbo coeficients taking into consideration both boost by gear and scramble
      end
    end

    for i = 1, loopLimit do
      for k, v in pairs(assignedEngine.torqueCurve) do
        if type(k) == "number" and k < assignedEngine.maxRPM then
          local toSub = assignedEngine.friction + (assignedEngine.dynamicFriction * k * rpmToAV)
          for j = 1, 2 do
            --i: gear index
            --(j == 1) --> scramble disabled, (j == 2) --> scramble enabled
            --k engine
            AlsTable.torqueCurveAtSeaLevel[i][j][k + 1] = (v * (turboCoefs[i][j][k] or 0)) - toSub --Calculate the torque the engine would produce at sea level
          end
        end
      end
    end

    --Optimization
    turboCoefs = nil
  end

  M.updateGFX = updateGFX
  M.updateFixedStep = updateFixedStep
  M.updateSounds = updateSounds
end

local function initSounds()
  local turboHissLoopFilename = turbo.hissLoopEvent or "event:>Vehicle>Forced_Induction>Turbo_01>turbo_hiss"
  turboHissLoop = obj:createSFXSource(turboHissLoopFilename, "AudioDefaultLoop3D", "TurbochargerWhine", assignedEngine.engineNodeID)
  local turboWhineLoopFilename = turbo.whineLoopEvent or "event:>Vehicle>Forced_Induction>Turbo_01>turbo_spin"
  turboWhineLoop = obj:createSFXSource(turboWhineLoopFilename, "AudioDefaultLoop3D", "TurbochargerWhine", assignedEngine.engineNodeID)

  turboWhinePitchPerAV = (turbo.whinePitchPer10kRPM or 0.05) * 0.01 * rpmToAV
  turboWhineVolumePerAV = (turbo.whineVolumePer10kRPM or 0.04) * 0.01 * rpmToAV
  electrics.values.turboWhineVolumePerAV = turboWhineVolumePerAV
  turboHissVolumePerPascal = (turbo.hissVolumePerPSI or 0.04) * invPascalToPSI

  bovSoundVolumeCoef = turbo.bovSoundVolumeCoef or 0.3
  bovSoundPressureCoef = turbo.bovSoundPressureCoef or 0.3
  local bovSoundFileName = turbo.bovSoundFileName or "event:>Vehicle>Forced_Induction>Turbo_01>turbo_bov"
  bovSound = obj:createSFXSource(bovSoundFileName, "AudioDefaultLoop3D", "Bov", assignedEngine.engineNodeID)

  flutterSoundVolumeCoef = turbo.flutterSoundVolumeCoef or 0.3
  flutterSoundPressureCoef = turbo.flutterSoundPressureCoef or 0.3
  local flutterSoundFileName = turbo.flutterSoundFileName or "event:>Vehicle>Forced_Induction>Turbo_02>turbo_bov"
  flutterSound = obj:createSFXSource(flutterSoundFileName, "AudioDefaultLoop3D", "Flutter", assignedEngine.engineNodeID)

  obj:setVolume(bovSound, 0)
  obj:setVolume(flutterSound, 0)
  obj:stopSFX(bovSound)
  obj:stopSFX(flutterSound)
end

local function resetSounds()
end

function getTorqueCoefs(gear, scramble)
  local coefs = {}
  scramble = scramble or 2 --If the caller is not in this script it does not pass any parameter so it is needed to assign it a default value
  --we can't know the actual wastegate limit for sure since it's a feedback loop with the pressure, so we just estimate it.
  --lower wastegate ranges lead to more accurate results.
  local estimatedWastegateLimit
  if AlsTable.isBoostBySpeed then
    estimatedWastegateLimit = AlsTable.boostAtSpeed[scramble][AlsTable.boostAtSpeedCount] * invPascalToPSI
  elseif gear then
    estimatedWastegateLimit = (wastegateStart[gear][scramble] + wastegateRange[gear][scramble] * 0.5) * invPascalToPSI
  else
    estimatedWastegateLimit = (maxWastegateStart[scramble] + maxWastegateRange[scramble] * 0.5) * invPascalToPSI
  end

  for k, _ in pairs(assignedEngine.torqueCurve) do
    if type(k) == "number" and k < assignedEngine.maxRPM then
      local rpm = floor(k)
      local turboAV = sqrt(max((0.9 * rpm * rpmToAV * invEngMaxAV * (turbo.turboExhaustCurve[rpm] or 1) * maxExhaustPower - frictionCoef), 0) / backPressureCoef)
      turboAV = min(turboAV, maxTurboAV)
      local turboRPM = floor(turboAV * avToRPM)
      local pressure = turbo.turboPressureCurve[turboRPM] or 0 --pressure without respecting the wastegate
      local actualPressure = min(pressure, estimatedWastegateLimit) --limit the pressure to what the wastegate allows
      coefs[k + 1] = (1 + 0.0000087 * actualPressure * psiToPascal * (turbo.turboEfficiencyCurve[rpm] or 0))
    end
  end

  return coefs
end

-- public interface
M.init = init
M.initSounds = initSounds
M.resetSounds = resetSounds
M.updateSounds = nop
M.reset = reset
M.updateGFX = nop
M.updateFixedStep = nop
M.getTorqueCoefs = getTorqueCoefs
M.getNeededPressure = getNeededPressure

return M
