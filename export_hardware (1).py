import subprocess
import tkinter as tk
from datetime import datetime


def ps(command):
    """Run a PowerShell command and return its text output."""
    try:
        result = subprocess.run(
            ["powershell.exe", "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", command],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=45,
        )
        return (result.stdout or result.stderr).strip()
    except Exception as exc:
        return f"[Komut hatası: {exc}]"


def main():
    report = f"""Dell Hackintosh Donanım Raporu
Oluşturulma: {datetime.now().isoformat(timespec='seconds')}

=== SİSTEM / BIOS ===
{ps("Get-CimInstance Win32_ComputerSystem | Select-Object Manufacturer,Model,SystemType,TotalPhysicalMemory | Format-List")}
{ps("Get-CimInstance Win32_BIOS | Select-Object Manufacturer,SMBIOSBIOSVersion,ReleaseDate | Format-List")}

=== İŞLEMCİ ===
{ps("Get-CimInstance Win32_Processor | Select-Object Name,NumberOfCores,NumberOfLogicalProcessors,MaxClockSpeed,SocketDesignation | Format-List")}

=== RAM ===
{ps("Get-CimInstance Win32_PhysicalMemory | Select-Object Manufacturer,PartNumber,Capacity,Speed,DeviceLocator | Format-Table -AutoSize")}

=== GRAFİK / EKRAN ===
{ps("Get-CimInstance Win32_VideoController | Select-Object Name,PNPDeviceID,DriverVersion,VideoModeDescription | Format-List")}

=== AĞ ADAPTÖRLERİ (Wi-Fi / Bluetooth / Ethernet) ===
{ps("Get-CimInstance Win32_PnPEntity | Where-Object {$_.Class -in @('Net','Bluetooth')} | Select-Object Name,Manufacturer,PNPDeviceID,Status | Format-List")}

=== TÜM PNP DONANIMLARI VE KİMLİKLERİ ===
{ps("Get-CimInstance Win32_PnPEntity | Where-Object {$_.PNPDeviceID -match 'PCI|USB|HDAUDIO|ACPI'} | Select-Object Class,Name,Manufacturer,PNPDeviceID,Status | Sort-Object Class,Name | Format-List")}

=== SES ===
{ps("Get-CimInstance Win32_SoundDevice | Select-Object Name,Manufacturer,PNPDeviceID,Status | Format-List")}

=== DİSKLER ===
{ps("Get-CimInstance Win32_DiskDrive | Select-Object Model,InterfaceType,MediaType,Size,PNPDeviceID | Format-List")}

=== EKRAN ÇÖZÜNÜRLÜĞÜ ===
{ps("Get-CimInstance Win32_VideoController | Select-Object Name,CurrentHorizontalResolution,CurrentVerticalResolution,CurrentRefreshRate | Format-Table -AutoSize")}

=== BATARYA ===
{ps("Get-CimInstance Win32_Battery | Select-Object Name,Manufacturer,DeviceID,Status,EstimatedChargeRemaining | Format-List")}

=== TOUCHPAD / KLAVYE ===
{ps("Get-CimInstance Win32_PnPEntity | Where-Object {$_.Name -match 'Touchpad|Trackpad|I2C|Keyboard|HID'} | Select-Object Name,Manufacturer,PNPDeviceID,Status | Format-List")}

=== WINDOWS SÜRÜMÜ ===
{ps("Get-CimInstance Win32_OperatingSystem | Select-Object Caption,Version,BuildNumber,OSArchitecture | Format-List")}

Not: Bu rapor parola, kişisel dosya veya ürün anahtarı içermez. MAC adresleri özellikle toplanmamıştır.
"""

    # Save a local copy next to the script.
    output_file = "hardware_report.txt"
    with open(output_file, "w", encoding="utf-8") as f:
        f.write(report)

    # Copy report to the Windows clipboard using tkinter (built into normal Python).
    try:
        root = tk.Tk()
        root.withdraw()
        root.clipboard_clear()
        root.clipboard_append(report)
        root.update()
        # Keep the clipboard alive briefly while Windows receives the data.
        root.after(1500, root.destroy)
        root.mainloop()
        clipboard_status = "Rapor panoya kopyalandı."
    except Exception as exc:
        clipboard_status = f"Pano kopyalanamadı: {exc}"

    print(report)
    print(f"\n{clipboard_status}")
    print(f"Ayrıca dosya oluşturuldu: {output_file}")
    input("Kapatmak için Enter'a basın...")


if __name__ == "__main__":
    main()
