/*
this file is part of notepad++
Copyright (C)2003 Don HO ( donho@altern.org )

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either
version 2 of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
*/

#ifndef COLUMNEDITOR_H
#define COLUMNEDITOR_H

#ifndef COLUMNEDITOR_RC_H
#include "columnEditor_rc.h"
#endif //COLUMNEDITOR_RC_H

class ScintillaEditView;

const bool activeText = true;
const bool activeNumeric = false;

class ColumnEditorDlg : public StaticDialog
{
public :
	ColumnEditorDlg() : StaticDialog() {};

	void init(HINSTANCE hInst, HWND hPere, ScintillaEditView **ppEditView) {
		Window::init(hInst, hPere);
		if (!ppEditView)
			throw std::runtime_error("StaticDialog::init : ppEditView is null.");
		_ppEditView = ppEditView;
	};

	virtual void create(int dialogID, bool isRTL = false) {
		StaticDialog::create(dialogID, isRTL);
	};

	void doDialog(bool isRTL = false) {
		if (!isCreated())
			create(IDD_COLUMNEDIT, isRTL);
		bool isTextMode = (BST_CHECKED == ::SendDlgItemMessage(_hSelf, IDC_COL_TEXT_RADIO, BM_GETCHECK, 0, 0));
		display();
		::SetFocus(::GetDlgItem(_hSelf, isTextMode?IDC_COL_TEXT_EDIT:IDC_COL_INITNUM_EDIT));
	};

    virtual void display(bool toShow = true) const;

	void switchTo(bool toText);

	UCHAR getFormat();

protected :
	virtual BOOL CALLBACK run_dlgProc(UINT message, WPARAM wParam, LPARAM lParam);

private :

    ScintillaEditView **_ppEditView;


};
#endif// COLUMNEDITOR_H
